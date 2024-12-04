import os

# Converts lean code to latex.
def convert(lean):
    return r'\begin{leancode}' + '\n' + lean + '\n' + r'\end{leancode}'

for root, dirs, files in os.walk('ConNF'):
    path = root.split(os.sep)
    newroot = os.path.join('latex', 'generated', *path[1:])
    os.makedirs(newroot, exist_ok=True)
    for file in files:
        if file != 'Code.lean':
            continue
        with open(os.path.join(root, file)) as f:
            content = f.read()
        with open(os.path.join(newroot, file.removesuffix('.lean') + '.latex'), 'w') as f:
            f.write(convert(content))
