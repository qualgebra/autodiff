import re
import pandas as pd 

def processT(x: object):
    t = x.strip()
    if t.endswith('ms'):
        t = t.removesuffix('ms')
        return float(t)
    else: 
        if t.endswith('s'):
            t = t.removesuffix('s')
            return 1000*float(t)
        else:
            return x

def lookup(m, v):
    for x in m:
        if v == x:
            return True
    return False

i = 'log.txt'
o = 'stats.txt'

df = pd.read_csv(i)
df['t1'] = df['t1'].map(processT)
df['t2'] = df['t2'].map(processT)
df['t3'] = df['t3'].map(processT)
df['t4'] = df['t4'].map(processT)

with open('univ_domain.txt', 'r') as dom_file:
    content = dom_file.readlines()
    indices = set(map(int, content))
    df['universal'] = df['idx'].apply(lambda x: lookup(indices, x))
        
df.to_csv(o, index=False)
