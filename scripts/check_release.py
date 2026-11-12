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
PROBE_SOURCES={'Axioms':'Axioms','Providers':'Providers','ConstantWindow':'ConstantWindowCheck','SourceDomains':'SourceScopeCheck','PalomarPilot':'PalomarPilotAxioms','PalomarAppendix':'PalomarAppendixAxioms'}
PALOMAR_AUDIT_IMPORTS={'verification/PalomarPilotAxioms.lean':'Palomar.Pilot.Solution','verification/PalomarAppendixAxioms.lean':'Palomar.AppendixA.Solution'}
COMPARATOR_KEYS={'challenge_module','solution_module','theorem_names','definition_names','permitted_axioms','enable_nanoda'}
REQUIRED_COMPARATOR_KEYS={'challenge_module','solution_module','theorem_names','permitted_axioms'}
DECL_COMMAND=re.compile(r'^[ \t]*(?:(?:public|protected|noncomputable)[ \t]+)*(namespace|end|theorem|lemma|def|abbrev|opaque|instance|example|axiom|constant|inductive|structure|class)\b([^\n]*)',re.M)
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
def masked_code(text):
 return ''.join(t if k=='code' else ''.join('\n' if c=='\n' else ' ' for c in t) for k,t in pieces(text))
def imports(text):
 out=[]
 for line in masked_code(text).splitlines():
  m=re.match(r'\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(.+)',line)
  if m:out.extend(m.group(1).split())
 return out
def check_proof_tokens(rel,text,challenge_names=None):
 tokens=command_tokens(text)
 for kind,token in tokens:
  if kind=='code' and (token in {'admit','axiom'} or (token=='sorry' and challenge_names is None)):
   raise ValueError('Forbidden proof token: '+rel+':'+token)
 if challenge_names is not None:check_challenge_text(text,challenge_names)
def check_challenge_text(text,names):
 """Allow one terminal := by sorry per compared theorem, with no other holes."""
 if not names or len(names)!=len(set(names)):raise ValueError('Invalid challenge declaration set')
 code=masked_code(text);events=list(DECL_COMMAND.finditer(code));namespace=[];found=[]
 for i,event in enumerate(events):
  kind,tail=event.group(1),event.group(2).strip()
  if kind=='namespace':
   if not re.fullmatch(r"[^\W\d][\w'.]*",tail):raise ValueError('Unsupported challenge namespace')
   namespace.append(tail);continue
  if kind=='end':
   if namespace:namespace.pop()
   continue
  block=text[event.start():events[i+1].start() if i+1<len(events) else len(text)]
  tokens=command_tokens(block);holes=[j for j,t in enumerate(tokens) if t==('code','sorry')]
  if not holes:continue
  match=re.match(r"([^\W\d][\w'.]*)",tail)
  full='.'.join(namespace+[match.group(1)]) if match else ''
  if kind!='theorem' or full not in names:raise ValueError('Hole outside compared theorem: '+full)
  if len(holes)!=1 or tokens[-4:]!=[('code',':'),('code','='),('code','by'),('code','sorry')]:
   raise ValueError('Challenge proof must be exactly := by sorry: '+full)
  found.append(full)
 total=sum(t==('code','sorry') for t in command_tokens(text))
 if len(found)!=total or sorted(found)!=sorted(names):raise ValueError('Challenge hole/declaration-set mismatch')
def check_challenge_config(spec,config):
 if not REQUIRED_COMPARATOR_KEYS<=set(config) or not set(config)<=COMPARATOR_KEYS:
  raise ValueError('Unsupported comparator configuration keys')
 if config['challenge_module'].replace('.','/')+'.lean'!=spec['path']:
  raise ValueError('Challenge/config module mismatch')
 if config['solution_module'].replace('.','/')+'.lean'!=spec['solution_path']:
  raise ValueError('Solution/config module mismatch')
 if config['theorem_names']!=spec['declarations'] or config.get('definition_names',[])!=[]:
  raise ValueError('Challenge/config declaration mismatch')
 if set(config['permitted_axioms'])!={'propext','Quot.sound','Classical.choice'} or config.get('enable_nanoda') is not True:
  raise ValueError('Comparator axiom/kernel policy mismatch')
def load_challenges():
 data=json.loads((ROOT/'verification/expected-challenge-holes.json').read_text())
 if data['schema_version']!=1:raise ValueError('Unknown challenge-hole schema')
 specs=data['challenges'];expected={'Palomar/Pilot/Challenge.lean','Palomar/AppendixA/Challenge.lean'}
 if len(specs)!=2 or {s['path'] for s in specs}!=expected:raise ValueError('Challenge allowlist mismatch')
 for spec in specs:
  path=ROOT/spec['path'];text=path.read_text()
  if sha(path)!=spec['sha256']:raise ValueError('Changed approved challenge: '+spec['path'])
  if len(text.splitlines())>1000 or path.stat().st_size>100*1024:raise ValueError('Challenge size limit: '+spec['path'])
  check_challenge_config(spec,json.loads((ROOT/spec['config']).read_text()))
  check_proof_tokens(spec['path'],text,spec['declarations'])
  if not imports(text) or any(m!='Mathlib' and not m.startswith('Mathlib.') for m in imports(text)):
   raise ValueError('Challenge imports must be Mathlib only: '+spec['path'])
  if not (ROOT/spec['solution_path']).is_file():raise ValueError('Missing challenge Solution')
 return {s['path']:s for s in specs}
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
 challenges=load_challenges()
 lean=[p for p in files if p.suffix=='.lean'];module_paths={str(p.relative_to(ROOT))[:-5].replace('/','.') for p in lean};graph={}
 for p in lean:
  rel=str(p.relative_to(ROOT));text=p.read_text();tokens=command_tokens(text)
  if len(text.splitlines())>10000:raise ValueError('Lean file exceeds 10000 physical lines: '+rel)
  if not tokens or tokens[0]!=('code','module'):raise ValueError('Missing module header: '+rel)
  check_proof_tokens(rel,text,challenges[rel]['declarations'] if rel in challenges else None)
  if re.search(r'\b(?:debug\.skipKernelTC|debug\.skipRecursorCheck)\b',text):raise ValueError('Disabled kernel check: '+rel)
  im=imports(text)
  for m in im:
   if m.endswith('.Challenge') or m in {s['path'][:-5].replace('/','.') for s in challenges.values()}:
    raise ValueError('Challenge import is forbidden: '+rel+':'+m)
   if (m.startswith(('DirectedDistances.','verification.','Palomar.')) or m=='DirectedDistances') and m not in module_paths:raise ValueError('Missing project import: '+m)
   if m.startswith('Palomar.'):
    if PALOMAR_AUDIT_IMPORTS.get(rel)!=m:raise ValueError('Palomar import outside exact solution audit: '+rel+':'+m)
   elif not (m=='DirectedDistances' or m.startswith(('DirectedDistances.','Mathlib.','Init.','Lean.')) or m in {'Mathlib','Init','Lean','verification.ConstantWindow','verification.SourceBoundaryDomain','verification.SourceBoundaryChanneled'}):raise ValueError('Undeclared import root: '+m)
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
 for label,filename in PROBE_SOURCES.items():
  names=re.findall(r'^#print axioms (\S+)',(ROOT/'verification'/(filename+'.lean')).read_text(),re.M)
  if names!=exp['probes'][label]:raise ValueError('Probe source changed: '+label)
 for spec,label in [(challenges['Palomar/Pilot/Challenge.lean'],'PalomarPilot'),(challenges['Palomar/AppendixA/Challenge.lean'],'PalomarAppendix')]:
  if exp['probes'][label]!=spec['declarations']:raise ValueError('Challenge/solution audit-set mismatch: '+label)
 print(json.dumps({'status':'PASS','files':len(files),'lean_files':len(lean),'project_modules_reachable':len(seen),'paper_entries':90,'paper_exports':len(exp['paper_exports']),'semantic_roots':len(imports((ROOT/'DirectedDistances/DeliveryVerificationRoot.lean').read_text())),'challenge_files':len(challenges),'deliberate_compared_holes':sum(len(s['declarations']) for s in challenges.values())}))
def main():
 p=argparse.ArgumentParser();p.add_argument('--axioms',choices=list(PROBE_SOURCES));p.add_argument('--log');a=p.parse_args()
 if a.axioms:
  if not a.log:p.error('--log is required with --axioms')
  axiom_log(a.axioms,a.log)
 else:check()
if __name__=='__main__':main()
