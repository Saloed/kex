import json
from typing import Dict

import numpy as np

from collections import defaultdict


def main():
    with open('stats.json', 'r') as f:
        current_stats = json.load(f)

    with open('stats.txt') as f:
        data = f.readlines()

    task_and_time = [[x.strip() for x in it.split('--')] for it in data]
    task_and_time = [(name, float(time)) for name, time in task_and_time]
    task_groups = group_by(task_and_time, key=lambda x: x[0], value=lambda x: x[1])
    current_stats_groups = {it['task']: it['all'] for it in current_stats}
    all_groups = merge(task_groups, current_stats_groups)

    stats = [
        {
            'task': name,
            'mean': float(np.mean(times)),
            'std': float(np.std(times)),
            'all': times
        }
        for name, times in all_groups
    ]
    with open('stats1.json', 'w') as f:
        json.dump(stats, f)


def merge(left: Dict[str, list], right: Dict[str, list]) -> Dict[str, list]:
    result = defaultdict(list)
    result.update(left)
    for key, value in right.items():
        result[key] += value
    return dict(result)


def group_by(data, key, value):
    grouped = defaultdict(list)
    for it in data:
        grouped[key(it)].append(value(it))
    return dict(grouped)


if __name__ == '__main__':
    main()
