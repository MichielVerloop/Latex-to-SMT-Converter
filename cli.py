import click

from latex_to_smt import convert, get_globals


@click.command()
@click.argument("formula")
@click.option("-g", "--global_vars", default="",
              help="Global variables that should be used, of the form 'x = y,y = z'.")
@click.option("-n", "--num_type", default="Int",
              help="The default type of number that is converted to when detecting numerical types. Should either be "
                   "Int (default) or Real")
@click.option("-d", "--default_type", default="Int",
              help="The default type for variables that could not be inferred. By default, this is set to Int.")
def handle_cli(formula, global_vars, num_type, default_type):
    """Converts a formula in LaTeX format to smt."""
    if formula == "":
        print("Throwing error")
        raise ValueError("Argument 'formula' should not be empty.")
    result = convert(formula, get_globals(global_vars), num_type, default_type)
    print(result)


if __name__ == '__main__':
    handle_cli()
