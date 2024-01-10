use std::fs;
use std::fs::File;
use std::io::Write;
use super::super::parse_cnf;

// Helper function to create a test CNF file
fn create_test_cnf_file(content: &str, filename: &str) {
    let mut file = File::create(filename).unwrap();
    write!(file, "{}", content).unwrap();
}

// Helper function to clean up a test file
fn cleanup_test_file(filename: &str) {
    fs::remove_file(filename).unwrap_or_default();
}

#[test]
fn test_successful_parsing() {
    let filename = "test_cnf_success.cnf";
    create_test_cnf_file("p cnf 3 2\nc comment line\n1 -2 0\n-3 1 0", filename);

    let solver_state = parse_cnf(filename).unwrap();
    cleanup_test_file(filename); // Clean up after test

    assert_eq!(solver_state.num_variables, 3);
    assert_eq!(solver_state.num_clauses(), 2);
}

#[test]
fn test_invalid_format() {
    let filename = "test_cnf_invalid_format.cnf";
    create_test_cnf_file("invalid content", filename);

    let result = parse_cnf(filename);
    cleanup_test_file(filename); // Clean up after test

    assert!(result.is_err());
}

#[test]
fn test_missing_cnf_header() {
    let filename = "test_cnf_missing_header.cnf";
    create_test_cnf_file("1 -2 0\n-3 1 0", filename);

    let result = parse_cnf(filename);
    cleanup_test_file(filename); // Clean up after test

    assert!(result.is_err());
}

#[test]
fn test_file_not_found() {
    let filename = "non_existent.cnf";

    let result = parse_cnf(filename);
    // No cleanup needed as the file does not exist

    assert!(result.is_err());
}


#[test]
fn test_parse_unit_clauses() {
    let filename = "test_cnf_unit_clauses.cnf";
    create_test_cnf_file("p cnf 3 2\n1 0\n-2 0", filename);

    let solver_state = parse_cnf(filename).unwrap();
    cleanup_test_file(filename); // Clean up after test

    assert_eq!(solver_state.num_variables, 3);
}


