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

# Continuous integration task.
@task
def ci(ctx):
    env = os.environ.copy()
    env["PATH"] = env["HOME"] + "/.elan/bin:" + env["PATH"]
    subprocess.run(["leanproject", "up"], env=env, check=True)
    subprocess.run(["leanproject", "build"], env=env, check=True)
    # Call these tasks afterwards.
    subprocess.run(["inv", "all", "html"], env=env, check=True)
