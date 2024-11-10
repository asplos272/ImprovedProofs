names = [
    "FixIBData", "FixIDData", "FixIIAGO_WritePull", "FixIIAGO_WritePullDrop",
    "FixIMADData", "FixIMADGO", "FixIMAGO", "FixIMDData", "FixISADData",
    "FixISADGO", "FixISAGO", "FixISDData", "FixISDIData", "FixISDSnpInv",
    "FixInvalidDirtyEvict", "FixInvalidLoad", "FixInvalidRdOwn",
    "FixInvalidRdShared", "FixInvalidStore", "FixMADData", "FixMADRspIFwdM",
    "FixMARspIFwdM", "FixMARspIHitSE", "FixMBData", "FixMDData",
    "FixMIAGO_WritePull", "FixMIASnpDataInvalid", "FixMIASnpDataShared",
    "FixMIASnpInv", "FixModifiedDirtyEvict", "FixModifiedDirtyEvictPrevious",
    "FixModifiedEvict", "FixModifiedLoad", "FixModifiedRdOwn",
    "FixModifiedRdShared", "FixModifiedSnpDataInvalid",
    "FixModifiedSnpDataShared", "FixModifiedSnpInv", "FixModifiedStore",
    "FixSADData", "FixSADRspIFwdM", "FixSADRspSFwdM", "FixSARspIFwdM",
    "FixSARspSFwdM", "FixSBData", "FixSDData", "FixSIACGO",
    "FixSIAGO_WritePull", "FixSIAGO_WritePullDrop", "FixSIASnpInv",
    "FixSMADData", "FixSMADGO", "FixSMADSnpInv", "FixSMAGO", "FixSMDData",
    "FixSharedDirtyEvict", "FixSharedEvict", "FixSharedLoad",
    "FixSharedRdOwn", "FixSharedRdOwnSelf", "FixSharedRdShared",
    "FixSharedSnpInv", "FixSharedStore", "FixShared_CleanEvictNoData_Last",
    "FixShared_CleanEvictNoData_NotLast", "FixShared_CleanEvict_Last",
    "FixShared_CleanEvict_NotLastData", "FixShared_CleanEvict_NotLastDrop",
    "FixSharedEvictData"
]

done_names = [
    "FixIMDData", "FixISDData", "FixShared_CleanEvict_Last", "FixShared_CleanEvict_NotLastData"
]

output_dir = "/Users/Chengsong/Documents/GitHub/betterProof/"

for name in names:
    if name not in done_names:
        original_file = f"~/Documents/GitHub/betterProof/{name}.thy"
        filled_file = f"{name}Filled.thy"
        sml_statement = f'val _ = end_to_end_fix "{original_file}" "{filled_file}" "{output_dir}"'
        clear_statement = f'val _ = {name} := nil'
        print(clear_statement)
        print(sml_statement)
