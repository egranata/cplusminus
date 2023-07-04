use std::{
    fs::File,
    io::Write,
    path::{Path, PathBuf},
};

fn status_msg(msg: String) {
    std::io::stdout().write_all(msg.as_bytes()).unwrap();
}

fn build_jit_tests(indir: &Path, outdir: &Path, pass: bool) {
    let mut outfile_path = PathBuf::from(outdir);
    let outfile_name = format!("test_jit{}.rs", if pass { "pass" } else { "fail" });
    outfile_path.push(outfile_name);
    let mut outfile_handle = File::create(&outfile_path).unwrap();
    let func_to_call = if pass {
        "expect_jit_pass"
    } else {
        "expect_jit_fail"
    };

    status_msg(format!(
        "building JIT tests from {} into {}\n",
        indir.display(),
        outfile_path.display()
    ));
    let iter = std::fs::read_dir(indir);
    if iter.is_err() {
        return;
    }
    let iter = iter.unwrap();
    for entry in iter {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_file() {
            continue;
        }
        let entry_path = entry.path();
        let is_cpm_file = entry_path.extension().map_or(false, |ext| ext == "cpm");
        if !is_cpm_file {
            continue;
        }
        let test_name = entry_path.file_stem().unwrap().to_str().unwrap();
        let content = format!(
            "#[test]\nfn jit_{test_name}() {{ {func_to_call}(include_str!(\"{}\")); }}\n",
            entry_path.as_os_str().to_str().unwrap()
        );
        write!(outfile_handle, "{content}").unwrap();
    }
}

fn build_aout_tests(indir: &Path, outdir: &Path, pass: bool) {
    let mut outfile_path = PathBuf::from(outdir);
    let outfile_name = format!("test_aout{}.rs", if pass { "pass" } else { "fail" });
    outfile_path.push(outfile_name);
    let mut outfile_handle = File::create(&outfile_path).unwrap();
    let func_to_call = if pass {
        "expect_aout_pass"
    } else {
        "expect_aout_fail"
    };

    status_msg(format!(
        "building a.out tests from {} into {}\n",
        indir.display(),
        outfile_path.display()
    ));
    let iter = std::fs::read_dir(indir);
    if iter.is_err() {
        return;
    }
    let iter = iter.unwrap();
    for entry in iter {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_file() {
            continue;
        }
        let entry_path = entry.path();
        let is_cpm_file = entry_path.extension().map_or(false, |ext| ext == "cpm");
        if !is_cpm_file {
            continue;
        }
        let test_name = entry_path.file_stem().unwrap().to_str().unwrap();
        let content = format!(
            "#[test]\nfn aout_{test_name}() {{ {func_to_call}(include_str!(\"{}\")); }}\n",
            entry_path.as_os_str().to_str().unwrap()
        );
        write!(outfile_handle, "{content}").unwrap();
    }
}

fn build_tests(indir: &mut Path, outdir: &Path) {
    status_msg(format!(
        "building C± tests from {} into {}\n",
        indir.display(),
        outdir.display()
    ));

    let mut jit_pass_indir = indir.to_path_buf();
    let mut jit_fail_indir = indir.to_path_buf();
    jit_pass_indir.push("jit");
    jit_pass_indir.push("pass");
    jit_fail_indir.push("jit");
    jit_fail_indir.push("fail");

    build_jit_tests(&jit_pass_indir, outdir, true);
    build_jit_tests(&jit_fail_indir, outdir, false);

    let mut aout_pass_indir = indir.to_path_buf();
    let mut aout_fail_indir = indir.to_path_buf();
    aout_pass_indir.push("aout");
    aout_pass_indir.push("pass");
    aout_fail_indir.push("aout");
    aout_fail_indir.push("fail");

    build_aout_tests(&aout_pass_indir, outdir, true);
    build_aout_tests(&aout_fail_indir, outdir, false);
}

fn main() {
    // if these variables are missing, bail out quick
    let env_manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let env_out_dir = std::env::var("OUT_DIR").unwrap();

    let path_manifest_dir = Path::new(&env_manifest_dir);
    let path_out_dir = Path::new(&env_out_dir);

    let mut path_manifest_dir = PathBuf::from(path_manifest_dir);
    let path_out_dir = PathBuf::from(path_out_dir);

    path_manifest_dir.push("tests");

    build_tests(&mut path_manifest_dir, &path_out_dir);
}
