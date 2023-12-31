use std::{
    fs::File,
    io::Write,
    path::{Path, PathBuf},
};

use serde::Deserialize;

fn status_msg(msg: String) {
    std::io::stdout().write_all(msg.as_bytes()).unwrap();
}

fn build_jit_test_code(func_to_call: &str, indir: &Path, outfile_path: &Path) {
    let mut outfile_handle = File::create(outfile_path).unwrap();
    status_msg(format!(
        "building tests from {} into {}\n",
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
            panic!(
                "unexpected !cpm file {} in JIT test tree",
                entry_path.display()
            );
        }
        let entry_path = entry_path.canonicalize().unwrap();
        let test_name = entry_path.file_stem().unwrap().to_str().unwrap();
        let content = format!(
            "#[test]\nfn jit_{test_name}() {{ let pf = PathBuf::from(\"{}\"); {func_to_call}(pf); }}\n",
            entry_path.as_os_str().to_str().unwrap()
        );
        write!(outfile_handle, "{content}").unwrap();
    }
}

fn build_jit_tests(indir: &Path, outdir: &Path, pass: bool) {
    let mut outfile_path = PathBuf::from(outdir);
    let outfile_name = format!("test_jit{}.rs", if pass { "pass" } else { "fail" });
    outfile_path.push(outfile_name);
    let func_to_call = if pass {
        "expect_jit_pass"
    } else {
        "expect_jit_fail"
    };
    build_jit_test_code(func_to_call, indir, &outfile_path);
}

#[derive(Deserialize)]
struct DriverTestConfig {
    source_files: Vec<String>,
    bom: bool,
    args: Option<Vec<String>>,
    diags_match: Option<Vec<String>>,
    diags_no_match: Option<Vec<String>>,
    stdout_match: Option<Vec<String>>,
    stderr_match: Option<Vec<String>>,
}

fn opt_vec_to_opt_str(inp: &Option<Vec<String>>) -> Option<String> {
    inp.as_ref().map(|x| {
        x.iter()
            .map(|x| format!("\"{x}\".to_string()"))
            .collect::<Vec<String>>()
            .join(",")
    })
}

fn opt_vec_to_opt_vec(inp: &Option<Vec<String>>, name: &str) -> String {
    opt_str_to_opt_vec(&opt_vec_to_opt_str(inp), name)
}

fn opt_str_to_opt_vec(os: &Option<String>, name: &str) -> String {
    format!(
        "     let {name}: Option<Vec<String>> = {};\n",
        if let Some(s) = os {
            format!("Some(vec![{s}])")
        } else {
            String::from("None")
        }
    )
}

#[allow(clippy::format_in_format_args)]
fn build_driver_test_code(func_to_call: &str, indir: &Path, outfile_path: &Path) {
    let mut outfile_handle = File::create(outfile_path).unwrap();
    status_msg(format!(
        "building tests from {} into {}\n",
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
        if !entry.file_type().unwrap().is_dir() {
            continue;
        }
        let entry_path = entry.path().canonicalize().unwrap();
        let test_name = entry_path.file_name().unwrap().to_str().unwrap();
        let test_json_path = entry_path.join("test.json");
        if !test_json_path.exists() {
            panic!(
                "directory {} does not contain a test configuration file",
                entry_path.display()
            );
        }
        let test_json_str = std::fs::read_to_string(test_json_path).unwrap();
        let test_descriptor: DriverTestConfig = serde_json::from_str(&test_json_str).unwrap();
        let args = opt_vec_to_opt_vec(&test_descriptor.args, "args");
        let diags_match = opt_vec_to_opt_str(&test_descriptor.diags_match);
        let diags_no_match = opt_vec_to_opt_str(&test_descriptor.diags_no_match);
        let stdout_match = opt_vec_to_opt_str(&test_descriptor.stdout_match);
        let stderr_match = opt_vec_to_opt_str(&test_descriptor.stderr_match);

        let sources: Vec<PathBuf> = test_descriptor
            .source_files
            .iter()
            .map(|sfn| entry_path.join(sfn).canonicalize().unwrap())
            .collect();
        let sources = sources
            .iter()
            .map(|x| format!("PathBuf::from(\"{}\")", x.display()))
            .collect::<Vec<String>>()
            .join(",");
        let dest = entry_path.join("a.out").display().to_string();
        write!(
            outfile_handle,
            "{}",
            format!("#[test]\nfn driver_{}() {{\n", test_name)
        )
        .expect("<io error>");
        write!(outfile_handle, "{}", args).expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            format!("    let sources: Vec<PathBuf> = vec![{sources}];\n")
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            opt_str_to_opt_vec(&diags_match, "diags_match")
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            opt_str_to_opt_vec(&diags_no_match, "diags_no_match")
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            opt_str_to_opt_vec(&stdout_match, "stdout_match")
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            opt_str_to_opt_vec(&stderr_match, "stderr_match")
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            format!("    let dest: PathBuf = PathBuf::from(\"{dest}\");\n")
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            format!("    remove_stale_files(&dest);\n")
        )
        .expect("<io error>");
        write!(outfile_handle, "{}", format!("    let opts = CompilerOptions{{ optimize: true, dump_bom:{}, ..Default::default()  }};\n", test_descriptor.bom)).expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            format!(
                "    {func_to_call}(&sources, &dest, &args, &opts, &diags_match, &diags_no_match, &stdout_match, &stderr_match);"
            )
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            format!("    remove_stale_files(&dest);\n")
        )
        .expect("<io error>");
        write!(outfile_handle, "{}", format!("    let opts = CompilerOptions{{ optimize: false, dump_bom:{}, ..Default::default()  }};\n", test_descriptor.bom)).expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            format!(
                "    {func_to_call}(&sources, &dest, &args, &opts, &diags_match, &diags_no_match, &stdout_match, &stderr_match);"
            )
        )
        .expect("<io error>");
        write!(
            outfile_handle,
            "{}",
            format!("    remove_stale_files(&dest);\n")
        )
        .expect("<io error>");
        write!(outfile_handle, "{}", format!("}}\n")).expect("<io error>");
    }
}

fn build_driver_tests(indir: &Path, outdir: &Path, pass: bool) {
    let mut outfile_path = PathBuf::from(outdir);
    let outfile_name = format!("test_driver{}.rs", if pass { "pass" } else { "fail" });
    outfile_path.push(outfile_name);
    let func_to_call = if pass {
        "expect_driver_pass"
    } else {
        "expect_driver_fail"
    };
    build_driver_test_code(func_to_call, indir, &outfile_path);
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

    let mut driver_pass_indir = indir.to_path_buf();
    let mut driver_fail_indir = indir.to_path_buf();
    driver_pass_indir.push("driver");
    driver_pass_indir.push("pass");
    driver_fail_indir.push("driver");
    driver_fail_indir.push("fail");

    build_driver_tests(&driver_pass_indir, outdir, true);
    build_driver_tests(&driver_fail_indir, outdir, false);
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

    println!("cargo:rerun-if-changed=tests");
}
