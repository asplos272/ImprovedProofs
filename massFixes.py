names = [
"FixInvalidStoreFilled",
"FixISDDataFilled", 
"FixMADDataFilled",
"FixMIAGO_WritePullFilled",
"FixMIASnpDataSharedFilled"

]

done_names = [
  
]

output_dir = "/Users/Chengsong/Documents/GitHub/betterProof/"

for name in names:
    if name not in done_names:
        original_file = f"~/Documents/GitHub/betterProof/{name}.thy"
        filled_file = f"{name}.thy"
        sml_statement = f'val _ = end_to_end_fix "{original_file}" "{filled_file}" "{output_dir}"'
        # clear_statement = f'val _ = {name} := nil'
        # print(clear_statement)
        print(sml_statement)
