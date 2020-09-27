import click

from latex_to_smt import convert, get_globals


@click.command()
@click.argument("formula")
@click.option("-g", "--global_vars", default = "", help = "Global variables that should be used, of the form 'x = y, "
                                                          "y = z'.")
def handle_cli(formula, global_vars):
    """Converts a formula in LaTeX format to smt."""
    if formula == "":
        print("Throwing error")
        raise ValueError("Argument 'formula' should not be empty.")
    result = convert(formula, get_globals(global_vars))
    print(result)


if __name__ == '__main__':
    handle_cli()