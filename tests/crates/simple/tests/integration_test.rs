extern crate simple;

// This file just exists so that we have an integration test, which causes the main lib crate to get
// compiled twice, once with --test and once without. We then make sure that we don't return
// duplicate matches in the non-test code in lib.rs.
