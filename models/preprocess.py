'''
Preprocessing script for Formal Verification of the MESI cache coherence
protocol in Spin/Promela.

Copyright (C) 2023  Luke Marzen
'''
import re
import subprocess
import sys


def preprocess(input_file_path, output_file_path):
    try:
        command = "spin -I " + input_file_path
        subprocess.check_output(command, shell=True, text=True)
    except subprocess.CalledProcessError as e:
        print(e.output)
        print(f"Command failed with error code {e.returncode}")
        exit(1)

    preproc_file_path = "pan.pre"

    with open(input_file_path, 'r') as input_file, open(preproc_file_path, 'r') as preproc_file, open(output_file_path, 'w') as output_file:
        pre_content = preproc_file.read()
        pattern = r'\s*::__EXPAND_SELECT__\(\s*([^,]+)\s*,\s*([^,]+)\s*,\s*([^)]+)\s*\)'
        matches = re.findall(pattern, pre_content)

        pattern = r'\s*__EXPAND_SELECT__\(\s*([^,]+)\s*,\s*([^,]+)\s*,\s*([^)]+)\s*\)'
        match_idx = 0
        for line in input_file:
            # Check if the line contains the target pattern
            match = re.match(pattern, line)
            if match:
                var_name, expr1, expr2 = matches[match_idx]
                try:
                    lower_bound = eval(expr1)
                    upper_bound = eval(expr2)
                    print(f'var_name: {var_name}, lower: {lower_bound}, upper: {upper_bound}')
                    output_file.write(f'if\n')
                    for i in range(lower_bound, upper_bound + 1):
                        output_file.write(f':: {var_name} = {i};\n')
                    output_file.write(f'fi\n') 

                except Exception as e:
                    print(f'Error evaluating expressions for var_name: {var_name}, expr1: {expr1}, expr2: {expr2}')
                    print(f'Error message: {str(e)}')

                match_idx = match_idx + 1
            else:
                # If the line doesn't match, write it as is
                output_file.write(line)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python", sys.argv[0], "input_file.c output_file.c")
        sys.exit(1)

    input_file_path = sys.argv[1]
    output_file_path = sys.argv[2]

    preprocess(input_file_path, output_file_path)
