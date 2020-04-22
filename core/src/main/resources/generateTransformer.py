import json

TYPES = {
    'PredicateState': 'State',
    'Predicate': 'Predicate',
    'Term': 'Term'
}


def generate_0(type_name, type_suffix):
    return 'is {name}{suffix} -> transform{name}(argument) as T'.format(name=type_name, suffix=type_suffix)


def generate_1(type_name, type_suffix):
    return 'is {name}{suffix} -> transform{name}{suffix}(argument) as T'.format(name=type_name, suffix=type_suffix)


def generate_when(type_name, delegates):
    return '''
    is {} -> when(argument) {{
        {}
        else -> unreachable {{ log.error("No {} transformer for $argument") }}
    }}
    '''.format(type_name, '\n'.join(delegates), type_name)


def generate_for_type(file_name, type_suffix):
    type_info = json.load(open('{}.json'.format(file_name)))
    impls = [it['name'] for it in type_info['inheritors']]
    delegates_0 = generate_when(file_name, [generate_0(it, type_suffix) for it in impls])
    delegates_1 = generate_when(file_name, [generate_1(it, type_suffix) for it in impls])
    return [delegates_0], [delegates_1]


def generate_func_def(idx, delegates):
    return '''
    private inline fun <reified T : TypeInfo> delegate{}(argument: T): T = when(argument){{
        {}
        else -> unreachable {{ log.error("No transformer for $argument") }}
    }}
    '''.format(idx, '\n'.join(delegates))


def generate():
    delegates_0, delegates_1 = [], []
    for file_name, type_suffix in TYPES.items():
        type_delegate_0, type_delegate_1 = generate_for_type(file_name, type_suffix)
        delegates_0 += type_delegate_0
        delegates_1 += type_delegate_1
    delegate_fn_0 = generate_func_def(0, delegates_0)
    delegate_fn_1 = generate_func_def(1, delegates_1)
    return delegate_fn_0, delegate_fn_1


def main():
    delegate_fn_0, delegate_fn_1 = generate()
    print(delegate_fn_0)
    print(delegate_fn_1)


if __name__ == '__main__':
    main()
