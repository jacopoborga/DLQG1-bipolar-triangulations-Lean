"""Small Lean lexical splitter used for release integrity checks."""
import re
WORD=re.compile(r"[^\W\d][\w']*",re.UNICODE)
def pieces(s):
    i=0;n=len(s);start=0
    while i<n:
        kind=None;end=None
        if s[i]=='«':
            kind='identifier';j=s.find('»',i+1)
            if j<0:raise ValueError('Unclosed Lean quoted identifier')
            end=j+1
        elif s.startswith('--',i):
            kind='comment';end=s.find('\n',i)
            if end<0:end=n
        elif s.startswith('/-',i):
            kind='comment';j=i+2;depth=1
            while j<n and depth:
                if s.startswith('/-',j):depth+=1;j+=2
                elif s.startswith('-/',j):depth-=1;j+=2
                else:j+=1
            if depth:raise ValueError('Unclosed Lean comment')
            end=j
        elif s[i]=="'":
            m=re.match(r"'(?:\\[^\n]|[^'\\\n])'",s[i:])
            if m:kind='literal';end=i+len(m.group())
        if kind is None and s[i]=='"':
            kind='literal';j=i+1;closed=False
            while j<n:
                if s[j]=='\\':j+=2
                elif s[j]=='"':j+=1;closed=True;break
                else:j+=1
            if not closed:raise ValueError('Unclosed Lean string')
            end=j
        if kind is not None:
            if start<i:yield 'code',s[start:i]
            yield kind,s[i:end];i=end;start=end
        else:i+=1
    if start<n:yield 'code',s[start:]
def change_words(s,mapping):return WORD.sub(lambda m:mapping.get(m.group(),m.group()),s)
def command_tokens(s):
    out=[]
    for k,t in pieces(s):
        if k=='comment':continue
        if k in {'literal','identifier'}:out.append((k,t))
        else:
            for m in re.finditer(r"[^\W\d][\w']*|\d+|[^\w\s]",t,re.UNICODE):out.append(('code',m.group()))
    return out
