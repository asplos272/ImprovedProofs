import os
import sys
import re

def create_fixer_thys(read_dir, output_dir, n):
    # Get all .thy files in the read directory (non-recursively) and sort them
    thy_files = sorted([f for f in os.listdir(read_dir) if f.endswith('.thy')])
    
    # Limit to the first n files
    thy_files = thy_files if n < 0 else thy_files[:n]

    for thy_file in thy_files:
        thy_file_path = os.path.join(read_dir, thy_file)
        thy_file_name = os.path.splitext(thy_file)[0]
        
        # Create a new directory in the output directory named after the thy_file
        new_dir = os.path.join(output_dir, thy_file_name)
        os.makedirs(new_dir, exist_ok=True)
        
        # Create a new .thy file in the new directory with the name of the original thy_file
        new_thy_file_path = os.path.join(new_dir, thy_file)
        with open(new_thy_file_path, 'w') as new_thy_file:
            with open(thy_file_path, 'r') as original_thy_file:
                content = original_thy_file.read()
                
                # Extract and modify the header
                header_match = re.search(r'theory\s+\S+\s+imports\s+(.+?)\s+begin', content, re.DOTALL)
                if header_match:
                    imports = header_match.group(1).strip().split()
                    modified_imports = ' '.join(f'BaseProof.{imp}' for imp in imports)
                    new_header = f'theory {thy_file_name}\n  imports {modified_imports} BaseProof.Fixer\nbegin\n'
                    new_thy_file.write(new_header)

                # Add the ML code block after the modified header
                new_thy_file.write(f'\nML \\<open>\nval _ = Fixer.fix_end_to_end \<^theory> "{thy_file_path}" "{os.path.basename(thy_file_path)}" "{output_dir}"\n\\<close>\n\nend\n')

        # Create the ROOT file in the new directory
        root_file_path = os.path.join(new_dir, 'ROOT')
        with open(root_file_path, 'w') as root_file:
            root_file.write(f'session "Temp" = BaseProof +\n')
            root_file.write(f'  options [document = false]\n')
            root_file.write(f'  theories\n')
            root_file.write(f'    {thy_file_name}\n')

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python fixers.py <read_dir> <output_dir> <n=number-of-files-(negative-means-all)>")
    else:
        read_dir = sys.argv[1]
        output_dir = sys.argv[2]
        n = int(sys.argv[3])

        create_fixer_thys(read_dir, output_dir, n)
