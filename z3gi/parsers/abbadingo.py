class ParseError(Exception):
    """A ParseError is raised when an incorrectly formatted line is encountered."""
    pass

def read(f, header=0):
    """Yields labeled strings or input/output traces from f.
    Returns as soon as it finds an incorrectly formatted line.

    Keyword arguments:
    f -- a file object
    header -- the number of lines to skip at the beginning (default: 0)
    """
    _ = [f.readline() for i in range(header)]
    for line in f:
        try:
            yield parse(line)
        except ParseError:
            break
    f.close()

def parse(line):
    """Parses a line that is formatted in Abbadingo format, and returns a labeled string or an input/output trace (depending on the line's format).
    The Abbadingo format is specified as follows:
    value n symbol1 symbol2 ... symboln
    If a symbol is formatted as 'input/output', value contains an output sequence.
    Raises a ParseError if line is not in the Abbadingo format.
    """

    try:
        fields = line.split()
        label = bool(int(fields[0]))
        inputs = []
        outputs = []
        for field in fields[2:]:
            symbol = field.split('/')
            if len(symbol) == 2:
                outputs.append(symbol[1])
            inputs.append(symbol[0])

        if len(outputs) == 0:
            return inputs, label
        else:
            return inputs, outputs
    except:
        raise ParseError(line)
