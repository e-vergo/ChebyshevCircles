from invoke import task

@task
def web(ctx):
    """Build the web version of the blueprint"""
    ctx.run("leanblueprint web")

@task
def pdf(ctx):
    """Build the PDF version of the blueprint"""
    ctx.run("leanblueprint pdf")

@task
def all(ctx):
    """Build both web and PDF versions"""
    ctx.run("leanblueprint all")

@task
def serve(ctx, port=8000):
    """Serve the blueprint locally"""
    ctx.run(f"leanblueprint serve --port {port}")

@task
def checkdecls(ctx):
    """Check that declarations in blueprint exist in Lean"""
    ctx.run("leanblueprint checkdecls")
