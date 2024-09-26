fn main() {
    let ac = autocfg::new();
    println!("cargo:rustc-check-cfg=cfg(has_doc_auto_cfg)");
    if ac.probe_raw("#![feature(doc_auto_cfg)]").is_ok() {
        println!("cargo:rustc-cfg=has_doc_auto_cfg");
    }
}
