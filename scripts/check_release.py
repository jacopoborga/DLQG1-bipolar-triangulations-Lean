#!/usr/bin/env python3
"""Check the source-only release and optional captured axiom output."""
import sys
sys.dont_write_bytecode=True
import argparse,hashlib,json,re
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from lean_syntax import pieces,command_tokens
ROOT=Path(__file__).resolve().parent.parent
BAD=re.compile(r'github\.com/jacopoborga/DirectedDistances(?:[/\s]|$)|(?:/(?:home|orcd|tmp)/[A-Za-z0-9_.-]+|\.lake/(?:armstrong|aws|campaign)|paper/source/[A-Za-z0-9_.-]+|docs/(?:frozen|standing|routine|paper-inventory))|-----BEGIN [A-Z ]*PRIVATE KEY-----|AKIA[0-9A-Z]{16}|gh[pousr]_[A-Za-z0-9]{20,}|sk-(?:proj-|ant-)?[A-Za-z0-9_-]{20,}')
FORBIDDEN_SUFFIXES={'.pdf','.tex','.zip','.tar','.gz','.tgz','.xz','.7z','.olean','.ilean','.pyc','.sqlite','.db','.pem'}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(4*1024*1024),b''):h.update(b)
 return h.hexdigest()
def source_files():
 out=[]
 for p in ROOT.rglob('*'):
  rel=p.relative_to(ROOT)
  if any(x in {'.git','.lake','__pycache__'} for x in rel.parts):continue
  if p.is_symlink():raise ValueError('Source symlink: '+str(rel))
  if p.is_file():out.append(p)
 return out
def imports(text):
 code=''.join(t if k=='code' else ''.join('\n' if c=='\n' else ' ' for c in t) for k,t in pieces(text))
 out=[]
 for line in code.splitlines():
  m=re.match(r'\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(.+)',line)
  if m:out.extend(m.group(1).split())
 return out
def axiom_log(label,path):
 expected=json.loads((ROOT/'verification/expected-exports.json').read_text())
 text=Path(path).read_text();seen={}
 pattern=r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
 for m in re.finditer(pattern,text):
  name=m.group(1)
  if name in seen:raise ValueError('Duplicate axiom output: '+name)
  seen[name]=[x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
 if set(seen)!=set(expected['probes'][label]):raise ValueError('Axiom export-set mismatch: '+label)
 actual=set(x for xs in seen.values() for x in xs)
 if not actual<=set(expected['allowed_axioms']) or 'sorryAx' in text:raise ValueError('Unexpected axioms: '+repr(actual))
 if re.search(r'(^|\n).*\berror:',text):raise ValueError('Lean error in axiom output')
 print(json.dumps({'probe':label,'exports':len(seen),'axioms':sorted(actual)}))
def check():
 manifest=json.loads((ROOT/'SOURCE-MANIFEST.json').read_text());files=source_files();expected=manifest['files'];actual={str(p.relative_to(ROOT)):p for p in files if p.name!='SOURCE-MANIFEST.json'}
 if set(actual)!=set(expected):raise ValueError('Public file-list mismatch')
 for n,p in actual.items():
  if p.suffix.lower() in FORBIDDEN_SUFFIXES:raise ValueError('Forbidden release artifact: '+n)
  if any(x in {'.aws','.codex','.claude','supplementary','Supplementary','paper','checkpoints','campaign'} for x in p.relative_to(ROOT).parts):raise ValueError('Excluded path: '+n)
  if sha(p)!=expected[n]['sha256'] or p.stat().st_size!=expected[n]['bytes']:raise ValueError('Changed release input: '+n)
  text=p.read_text()
  if BAD.search(text):raise ValueError('Private/credential reference: '+n)
 lean=[p for p in files if p.suffix=='.lean'];module_paths={str(p.relative_to(ROOT))[:-5].replace('/','.') for p in lean};graph={}
 for p in lean:
  rel=str(p.relative_to(ROOT));text=p.read_text();tokens=command_tokens(text)
  if not tokens or tokens[0]!=('code','module'):raise ValueError('Missing module header: '+rel)
  for kind,token in tokens:
   if kind=='code' and token in {'sorry','admit','axiom'}:raise ValueError('Forbidden proof token: '+rel+':'+token)
  if re.search(r'\b(?:debug\.skipKernelTC|debug\.skipRecursorCheck)\b',text):raise ValueError('Disabled kernel check: '+rel)
  im=imports(text)
  for m in im:
   if (m.startswith(('DirectedDistances.','verification.')) or m=='DirectedDistances') and m not in module_paths:raise ValueError('Missing project import: '+m)
   if not (m=='DirectedDistances' or m.startswith(('DirectedDistances.','Mathlib.','Init.','Lean.')) or m in {'Mathlib','Init','Lean','verification.ConstantWindow','verification.SourceBoundaryDomain','verification.SourceBoundaryChanneled'}):raise ValueError('Undeclared import root: '+m)
  graph[rel[:-5].replace('/','.')]=[m for m in im if m in module_paths]
 seen=set();todo=['DirectedDistances']
 while todo:
  m=todo.pop()
  if m not in seen:seen.add(m);todo.extend(graph.get(m,[]))
 math={m for m in graph if m=='DirectedDistances' or m.startswith('DirectedDistances.')}
 if seen!=math:raise ValueError('Unnecessary/unreachable project modules: '+repr(sorted(math-seen)))
 corr=json.loads((ROOT/'CORRESPONDENCE.json').read_text());exp=json.loads((ROOT/'verification/expected-exports.json').read_text())
 if len(corr['entries'])!=90 or len({x['label'] for x in corr['entries']})!=90:raise ValueError('90-entry correspondence mismatch')
 if {d['declaration'] for r in corr['entries'] for d in r['exports']}!=set(exp['paper_exports']):raise ValueError('Paper export-set mismatch')
 for label in ['Axioms','Providers']:
  names=re.findall(r'^#print axioms (\S+)',(ROOT/'verification'/(label+'.lean')).read_text(),re.M)
  if names!=exp['probes'][label]:raise ValueError('Probe source changed: '+label)
 for label,filename in [('SourceDomains','SourceScopeCheck')]:
  names=re.findall(r'^#print axioms (\S+)',(ROOT/'verification'/(filename+'.lean')).read_text(),re.M)
  if names!=exp['probes'][label]:raise ValueError('Probe source changed: '+label)
 print(json.dumps({'status':'PASS','files':len(files),'lean_files':len(lean),'project_modules_reachable':len(seen),'paper_entries':90,'paper_exports':len(exp['paper_exports']),'semantic_roots':len(imports((ROOT/'DirectedDistances/DeliveryVerificationRoot.lean').read_text()))}))
def main():
 p=argparse.ArgumentParser();p.add_argument('--axioms',choices=['Axioms','Providers','ConstantWindow','SourceDomains']);p.add_argument('--log');a=p.parse_args()
 if a.axioms:
  if not a.log:p.error('--log is required with --axioms')
  axiom_log(a.axioms,a.log)
 else:check()
if __name__=='__main__':main()
