"""Distinguish command information from references to retained declarations."""
def is_example_command(row, source):
    # Lean attaches a temporary `_example` constant to the `example` keyword.
    # Each such command is checked but does not add a named module declaration.
    # Identify the exact source token; never exempt a missing proof dependency.
    if row.get('kind')!='reference' or row.get('declaration') is not None:
        return False
    if not row.get('name','').endswith('._example'):
        return False
    span=row['range']
    return source[span['start']['byte']:span['end']['byte']]==b'example'
