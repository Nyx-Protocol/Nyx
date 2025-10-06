// Example: Advanced error handling patterns
//
// This example demonstrates:
// - Different error types and handling
// - Retryable vs fatal errors
// - Error categorization
// - Retry logic implementation

// Removed unused import: error::ErrorCategory (not used in this example)
use nyx_sdk::{Error, NyxStream, Result};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Error Handling Examples ===\n");

    example_timeout_error().await;
    example_disconnection_error().await;
    example_authentication_error().await;
    example_retry_logic().await;
    example_error_categorization().await;

    Ok(())
}

async fn example_timeout_error() {
    println!("1. Timeout Error Example");
    println!("-----------------------");

    let (mut _sender, mut receiver) = NyxStream::pair(1024);

    // Try to receive with short timeout (will timeout)
    match receiver.recv_with_timeout(100).await {
        Ok(Some(data)) => println!("Received: {:?}", data),
        Ok(None) => println!("Stream closed"),
        Err(Error::Timeout { duration_ms }) => {
            println!("✓ Caught timeout error after {}ms", duration_ms);
            println!(
                "  This error is retryable: {}",
                Error::timeout(duration_ms).is_retryable()
            );
        }
        Err(e) => println!("Other error: {}", e),
    }
    println!();
}

async fn example_disconnection_error() {
    println!("2. Disconnection Error Example");
    println!("----------------------------");

    let error = Error::disconnected("Network connection lost");
    println!("Error: {}", error);
    println!("Is retryable: {}", error.is_retryable());
    println!("Is fatal: {}", error.is_fatal());
    println!("Category: {}", error.category());
    println!();
}

async fn example_authentication_error() {
    println!("3. Authentication Error Example");
    println!("------------------------------");

    let error = Error::authentication_failed("Invalid token");
    println!("Error: {}", error);
    println!("Is retryable: {}", error.is_retryable());
    println!("Is fatal: {}", error.is_fatal());
    println!("Category: {}", error.category());
    println!();
}

async fn example_retry_logic() {
    println!("4. Retry Logic Example");
    println!("---------------------");

    // Use AtomicU32 instead of mutable static to avoid undefined behavior
    use std::sync::atomic::{AtomicU32, Ordering};
    static ATTEMPT: AtomicU32 = AtomicU32::new(0);

    // Simulate an operation that might fail
    let result = retry_operation(
        || async {
            let attempt = ATTEMPT.fetch_add(1, Ordering::SeqCst) + 1;
            if attempt < 3 {
                println!("  Attempt {} - simulating failure", attempt);
                Err(Error::timeout(1000))
            } else {
                println!("  Attempt {} - success!", attempt);
                Ok("Operation succeeded")
            }
        },
        5,
    )
    .await;

    match result {
        Ok(msg) => println!("✓ Final result: {}", msg),
        Err(e) => println!("✗ Failed after retries: {}", e),
    }
    println!();
}

async fn example_error_categorization() {
    println!("5. Error Categorization");
    println!("----------------------");

    let errors = vec![
        Error::timeout(5000),
        Error::disconnected("Connection lost"),
        Error::authentication_failed("Bad token"),
        Error::Config("Invalid configuration".into()),
        Error::Protocol("Invalid protocol".into()),
        Error::rate_limited("Too many requests"),
        Error::invalid_state("Invalid state"),
        Error::resource_exhausted("Out of memory"),
    ];

    for error in errors {
        println!("Error: {}", error);
        println!("  Category: {}", error.category());
        println!("  Retryable: {}", error.is_retryable());
        println!("  Fatal: {}", error.is_fatal());
        println!();
    }
}

// Retry logic implementation
async fn retry_operation<F, Fut, T>(mut op: F, max_attempts: u32) -> Result<T>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T>>,
{
    let mut attempt = 0;

    loop {
        match op().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                attempt += 1;

                if e.is_fatal() {
                    println!("  Fatal error detected, not retrying");
                    return Err(e);
                }

                if !e.is_retryable() {
                    println!("  Error is not retryable");
                    return Err(e);
                }

                if attempt >= max_attempts {
                    println!("  Max attempts ({}) reached", max_attempts);
                    return Err(e);
                }

                // Exponential backoff
                let delay = Duration::from_millis(100 * 2u64.pow(attempt - 1));
                println!("  Retrying in {:?}...", delay);
                sleep(delay).await;
            }
        }
    }
}
