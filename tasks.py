import os
import shutil
import sys
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
    if os.system("leanproject up") != 0:
        sys.exit("leanproject up failed")
    if os.system("leanproject build") != 0:
        sys.exit("leanproject build failed")
    # Call these tasks afterwards.
    os.system("inv all html")
