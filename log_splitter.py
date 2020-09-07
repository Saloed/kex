import os
import argparse
import re

parser = argparse.ArgumentParser(description='Split log file onto multiple files by given criteria')
parser.add_argument('logfile', type=str, help='log file to split')
parser.add_argument('criteria', type=str, help='file split condition')
parser.add_argument('--remove-time', default=False, action='store_true',
                    help='remove timestamps from log file entries')
args = parser.parse_args()

log_entry = re.compile('\\d+-\\d+-\\d+ \\d+:\\d+:\\d+\\.\\d+(.*)')


def split_file_name(split):
    filename, file_extension = os.path.splitext(args.logfile)
    return f'{filename}_{split}{file_extension}'


def write_split(index, buffer):
    split_name = split_file_name(index)
    with open(split_name, 'w', encoding='utf-8') as split_file:
        split_file.writelines(buffer)


def remove_time(line):
    match = log_entry.match(line)
    if match is None:
        return line
    return match.group(1)


def run():
    with open(args.logfile, 'r', encoding='utf-8') as logfile:
        line_buffer = []
        split_index = 0
        for line in logfile:
            if args.remove_time:
                line = remove_time(line)
            if args.criteria not in line:
                line_buffer.append(line)
                continue
            write_split(split_index, line_buffer)
            split_index += 1
            line_buffer = [line]
        if line_buffer:
            write_split(split_index, line_buffer)


if __name__ == '__main__':
    run()
