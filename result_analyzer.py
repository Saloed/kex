import os
import re
import enum
import json
import datetime
import pandas as pd
from collections import defaultdict


class Status(enum.Enum):
    UNKNOWN = 'UNKNOWN'
    TRIVIAL = 'TRIVIAL'
    PS_TRIVIAL = 'PS_TRIVIAL'
    NON_TRIVIAL = 'NON_TRIVIAL'


function_entry = re.compile('.*\[INFO \]\[.*\] - Analyze:(.*)')
function_start_entry = re.compile('(.*)\[INFO \]\[.*\] - (Analyze|Start analysis):(.*)')
result_entry = re.compile('(.*)\[INFO \]\[.*\] - Result (.*)\:')
log_entry = re.compile('\d+\-\d+\-\d+ \d+\:\d+\:\d+\.\d+.*')
criteria_entry = re.compile('RefinementCriteria\(type=(.*)\).*')


def get_function_set(file):
    lines = file.readlines()
    matches = (re.match(function_entry, line) for line in lines)
    matched_entries = (m for m in matches if m)
    functions = (m.group(1).strip() for m in matched_entries)
    return set(functions)


def analyze_result(result):
    result = [res.strip() for res in result]
    result = [res for res in result if res]
    if not result:
        return {'status': Status.UNKNOWN}
    is_refinements = result[0].startswith('Refinements')
    if not is_refinements:
        return {'status': Status.UNKNOWN}
    if len(result) == 1:
        return {'status': Status.TRIVIAL}
    parsed_res = []
    for line in result[1:]:
        criteria = re.match(criteria_entry, line)
        if criteria:
            parsed_res.append({'criteria': criteria.group(1), 'ps': []})
            continue
        if line.startswith(')'):
            continue
        parsed_res[-1]['ps'].append(line)
    for res in parsed_res:
        res['ps'] = '\n'.join(res['ps'])
    return {'status': Status.NON_TRIVIAL, 'data': parsed_res}


def get_results(file):
    parsed_results = []
    start_times = {}
    lines = file.readlines()
    is_result = False
    for line in lines:
        fn_start = re.match(function_start_entry, line)
        if fn_start:
            function_name = fn_start.group(3).strip()
            start_time = fn_start.group(1).strip()
            start_times[function_name] = start_time
        if is_result:
            is_log_entry = re.match(log_entry, line)
            if is_log_entry:
                is_result = False
                continue
            parsed_results[-1]['result'].append(line)
            continue

        function_result = re.match(result_entry, line)
        if not function_result:
            is_result = False
            continue
        function_name = function_result.group(2).strip()
        finish_time = function_result.group(1).strip()
        parsed_results.append({'name': function_name, 'start': start_times[function_name], 'finish': finish_time, 'result': []})
        is_result = True
    result = []
    for res in parsed_results:
        analyzed = analyze_result(res['result'])
        result.append({
            'name': res['name'],
            'start': res['start'],
            'finish': res['finish'],
            'status': analyzed['status'],
            'data': analyzed.get('data')
        })
    return result


def flat_non_trivial(data):
    result = []
    for item in data:
        if item['status'] == Status.UNKNOWN or item['status'] == Status.TRIVIAL:
            result.append({
                'name': item['name'],
                'start': item['start'],
                'finish': item['finish'],
                'criteria': None,
                'status': item['status'],
                'data': None
            })
            continue
        for criteria in item['data']:
            status = Status.NON_TRIVIAL
            ps = criteria['ps']
            if ps == '@S false':
                status = Status.PS_TRIVIAL
            result.append({
                'name': item['name'],
                'start': item['start'],
                'finish': item['finish'],
                'criteria': criteria['criteria'],
                'status': status,
                'data': ps
            })
    return result


def stats(file):
    with open(file) as f:
        functions = get_function_set(f)
    with open(file) as f:
        results = get_results(f)
        results = flat_non_trivial(results)
    return analyze(functions, results)


def analyze(all_functions, results):
    aggregated = {}
    for res in results:
        fn = res['name']
        current = aggregated.get(fn, Status.UNKNOWN)
        if current == Status.NON_TRIVIAL:
            continue
        if res['status'] == Status.UNKNOWN:
            aggregated[fn] = Status.UNKNOWN
        elif res['status'] == Status.TRIVIAL or res['status'] == Status.PS_TRIVIAL:
            aggregated[fn] = Status.TRIVIAL
        elif res['status'] == Status.NON_TRIVIAL:
            aggregated[fn] = Status.NON_TRIVIAL

    return {
        'total_functions': max(len(all_functions), len(aggregated)),
        'unknown': len([name for name, status in aggregated.items() if status == Status.UNKNOWN]),
        'trivial': len([name for name, status in aggregated.items() if status == Status.TRIVIAL]),
        'non_trivial': len([name for name, status in aggregated.items() if status == Status.NON_TRIVIAL]),
        'time_stats': analyze_timings(results),
        'raw': results
    }

def analyze_timings(results):
    deltas = [(from_iso_format(it['finish']) - from_iso_format(it['start'])).microseconds for it in results]
    status_timings = defaultdict(list)
    for it in results:
         start = from_iso_format(it['start'])
         finish = from_iso_format(it['finish'])
         delta = finish - start
         status_timings[it['status']].append(delta.microseconds)
    per_function = time_stats(deltas)
    per_status = {status: time_stats(timings) for status, timings in status_timings.items()}

    return {
        'per_function': stats_in_miliseconds(per_function),
        'per_status': {str(status): stats_in_miliseconds(it) for status, it in per_status.items()}
    }

def stats_in_miliseconds(stats):
    return {k: str(float(v) / 1000) for k,v in stats.items()}

def time_stats(timedeltas):
    if not timedeltas:
        return {}
    df = pd.DataFrame(timedeltas)
    return {
        'mean': df.mean(),
        '95%': df.quantile(0.95),
        '99%': df.quantile(0.99),
    }

def from_iso_format(time_str):
    fmt_str =  r"%Y-%m-%d %H:%M:%S.%f"
    return datetime.datetime.strptime(time_str, fmt_str)


class EnumEncoder(json.JSONEncoder):
    def default(self, obj):
        if type(obj) == Status:
            return {"__enum__": str(obj)}
        return json.JSONEncoder.default(self, obj)


base_path = os.path.join('tests', 'results')
analyzed_path = os.path.join(base_path, 'analyzed')
if not os.path.exists(analyzed_path):
    os.mkdir(analyzed_path)

format = '{} | {} | {} | {} | {} | {} | {} | {}'
print(format.format('project' , 'total' , 'non trivial' , 'trivial' , 'fn mean' , 'fn 99' , 'nt mean' , 'nt 99'))
for file in os.listdir(base_path):
    file_path = os.path.join(base_path, file)
    if not os.path.isfile(file_path):
        continue
    result_path = os.path.join(analyzed_path, '{}.json'.format(file))
    result = stats(file_path)
    if result['total_functions'] == 0:
        continue
    with open(result_path, 'w') as f:
        json.dump(result, f, cls=EnumEncoder)
    print(format.format(file, result['total_functions'], result['non_trivial'], result['trivial'],
     result['time_stats']['per_function']['mean'], result['time_stats']['per_function']['99%'],
     result['time_stats']['per_status']['Status.NON_TRIVIAL']['mean'], result['time_stats']['per_status']['Status.NON_TRIVIAL']['99%']))


