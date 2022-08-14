import os
import shutil
import subprocess
from pathlib import Path
from invoke import run, task

from mathlibtools.lib import LeanProject

from blueprint.tasks import web, bp, print_bp, serve

ROOT = Path(__file__).parent

@task
def decls(ctx):
    proj = LeanProject.from_path(ROOT)
    proj.pickle_decls(ROOT/'decls.pickle')

@task(decls, bp, web)
def all(ctx):
    shutil.rmtree(ROOT/'docs'/'blueprint', ignore_errors=True)
    shutil.copytree(ROOT/'blueprint'/'web', ROOT/'docs'/'blueprint')
    shutil.copy2(ROOT/'blueprint'/'print'/'print.pdf', ROOT/'docs'/'blueprint.pdf')

@task(web)
def html(ctx):
    shutil.rmtree(ROOT/'docs'/'blueprint', ignore_errors=True)
    shutil.copytree(ROOT/'blueprint'/'web', ROOT/'docs'/'blueprint')

@task
def doc(ctx):
    print("Making all.lean")
    subprocess.run(["bash", "mk_all.sh"], cwd = "scripts", check=True)

    print("Downloading doc-gen")
    if os.path.exists("doc-gen"):
        subprocess.run(["git", "fetch"], check=True, cwd="doc-gen")
        subprocess.run(["git", "reset", "--hard", "origin/master"], check=True, cwd="doc-gen")
    else:
        subprocess.run(["git", "clone", "https://github.com/leanprover-community/doc-gen.git"],
            check=True)

    files = ["src/entrypoint.lean", "src/export_json.lean", "src/lean_commit.lean",
        "color_scheme.js", "nav.js", "pygments-dark.css", "pygments.css", "search.js",
        "STIXlicense.txt", "STIXTwoMath.woff2", "style.css"]
    folders = ["static", "templates", "test"]

    print("Copying over doc-gen files")
    import shutil
    for file in files:
        shutil.copyfile("doc-gen/" + file, file)
    for folder in folders:
        shutil.copytree("doc-gen/" + folder, folder, dirs_exist_ok=True)

    print("Compiling documentation generator")
    subprocess.run(["lean", "--make", "src/entrypoint.lean"], check=True)
    with open("export.json", "w") as f:
        print("Generating documentation")
        subprocess.run(["lean", "--run", "src/entrypoint.lean"], stdout=f, check=True)

    print("Printing documentation to HTML")
    import sys
    sys.argv = [sys.argv[0], "-w", "https://leanprover-community.github.io/con-nf/docs/"]
    sys.path.insert(0, "doc-gen")
    import print_docs
    del print_docs.extra_doc_files[:]
    print_docs.copy_yaml_bib_files = lambda p: None
    print_docs.library_link_roots['con-nf'] = 'https://github.com/leanprover-community/con-nf/blob/main/src/'
    print_docs.main()

    print("Cleaning up doc-gen files")
    os.remove("export.json")
    for file in files:
        os.remove(file)
    for folder in folders:
        shutil.rmtree(folder)

    shutil.rmtree(ROOT/'docs'/'docs', ignore_errors=True)
    shutil.move(ROOT/'html', ROOT/'docs'/'docs')

# Continuous integration task.
@task
def ci(ctx):
    env = os.environ.copy()
    env["PATH"] = env["HOME"] + "/.elan/bin:" + env["PATH"]
    subprocess.run(["leanproject", "up"], env=env, check=True)
    subprocess.run(["leanproject", "build"], env=env, check=True)
    # Call these tasks afterwards.
    subprocess.run(["inv", "all", "html", "doc"], env=env, check=True)
    subprocess.run(["python3", "scripts/count_sorry.py"], env=env, check=True)
