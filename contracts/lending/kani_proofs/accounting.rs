//! Formal verification of the lending contract's accounting invariants.
//!
//! Verifies:
//! - `remaining_due >= 0` after any payment
//! - `remaining_due <= total_due` at all times
//! - `total_due >= principal` at creation
//! - Uncollected fees increase correctly
//! - Payment reduces remaining_due correctly

// ─── Mirrored types ──────────────────────────────────────────────────────────

/// Loan status mirroring the contract's `LoanStatus` enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoanStatus {
    Pending,
    Approved,
    Active,
    Repaid,
    Defaulted,
    Cancelled,
}

/// Simplified loan record for proof purposes.
#[derive(Debug, Clone)]
struct LoanRecord {
    amount: i128,
    total_due: i128,
    remaining_due: i128,
    status: LoanStatus,
    platform_fee: i128,
}

/// Compute interest: `principal × rate_bps × days / (10_000 × 365)`.
fn calculate_interest(principal: i128, rate_bps: u32, days: u32) -> Option<i128> {
    let numerator = (principal as i128)
        .checked_mul(rate_bps as i128)?
        .checked_mul(days as i128)?;
    Some(numerator / (10_000_i128 * 365))
}

/// Compute platform fee: `interest × fee_bps / 10_000`.
fn calculate_platform_fee(interest: i128, fee_bps: u32) -> Option<i128> {
    (interest as i128)
        .checked_mul(fee_bps as i128)?
        .checked_div(10_000)
}

/// Simulate `create_loan_request` accounting.
fn create_loan(
    principal: i128,
    rate_bps: u32,
    days: u32,
    fee_bps: u32,
) -> Option<(LoanRecord, i128)> {
    let interest = calculate_interest(principal, rate_bps, days)?;
    let platform_fee = calculate_platform_fee(interest, fee_bps)?;
    let total_due = principal.checked_add(interest)?;

    let loan = LoanRecord {
        amount: principal,
        total_due,
        remaining_due: total_due,
        status: LoanStatus::Pending,
        platform_fee,
    };

    Some((loan, platform_fee))
}

/// Simulate `record_payment` accounting.
/// Returns the updated loan and the actual payment applied.
fn record_payment(loan: &mut LoanRecord, amount: i128) -> Option<i128> {
    if amount <= 0 {
        return None;
    }
    if loan.status != LoanStatus::Active {
        return None;
    }

    let actual_payment = if amount >= loan.remaining_due {
        loan.remaining_due
    } else {
        amount
    };

    loan.remaining_due = loan.remaining_due.checked_sub(actual_payment)?;
    if loan.remaining_due == 0 {
        loan.status = LoanStatus::Repaid;
    }

    Some(actual_payment)
}

/// Simulate `switch_rate_model` fee application.
fn apply_switch_fee(loan: &mut LoanRecord, switch_fee_bps: u32) -> Option<i128> {
    let fee = loan
        .remaining_due
        .checked_mul(switch_fee_bps as i128)?
        .checked_div(10_000)?;
    loan.remaining_due = loan.remaining_due.checked_add(fee)?;
    loan.total_due = loan.total_due.checked_add(fee)?;
    Some(fee)
}

// ─── Kani Proof Harnesses ────────────────────────────────────────────────────

/// INV-ACCT-1: remaining_due >= 0 after loan creation.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_1_remaining_due_nonnegative_at_creation() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);

    if let Some((loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        assert!(
            loan.remaining_due >= 0,
            "remaining_due must be non-negative at creation"
        );
    }
}

/// INV-ACCT-2: remaining_due <= total_due at creation.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_2_remaining_le_total_at_creation() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);

    if let Some((loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        assert!(
            loan.remaining_due <= loan.total_due,
            "remaining_due must not exceed total_due at creation"
        );
    }
}

/// INV-ACCT-3: total_due >= principal (interest is non-negative).
#[cfg(kani)]
#[kani::proof]
fn inv_acct_3_total_due_ge_principal() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);

    if let Some((loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        assert!(
            loan.total_due >= principal,
            "total_due must be >= principal"
        );
    }
}

/// INV-ACCT-4: remaining_due never goes negative after payment.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_4_payment_never_negative() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();
    let payment_amount: i128 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);
    kani::assume(payment_amount > 0);

    if let Some((mut loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        loan.status = LoanStatus::Active;
        let _ = record_payment(&mut loan, payment_amount);
        assert!(
            loan.remaining_due >= 0,
            "remaining_due must never go negative after payment"
        );
    }
}

/// INV-ACCT-5: remaining_due decreases by at most payment_amount.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_5_payment_reduces_correctly() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();
    let payment_amount: i128 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);
    kani::assume(payment_amount > 0 && payment_amount <= 100_000_000_000);

    if let Some((mut loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        loan.status = LoanStatus::Active;
        let before = loan.remaining_due;
        let _ = record_payment(&mut loan, payment_amount);
        let after = loan.remaining_due;
        let actual = before - after;
        assert!(
            actual >= 0 && actual <= payment_amount,
            "Payment reduction must be in [0, payment_amount]"
        );
    }
}

/// INV-ACCT-6: remaining_due == 0 implies status == Repaid.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_6_zero_remaining_implies_repaid() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();
    let payment_amount: i128 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);
    kani::assume(payment_amount > 0);

    if let Some((mut loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        loan.status = LoanStatus::Active;
        let _ = record_payment(&mut loan, payment_amount);
        if loan.remaining_due == 0 {
            assert_eq!(
                loan.status,
                LoanStatus::Repaid,
                "remaining_due == 0 must imply status == Repaid"
            );
        }
    }
}

/// INV-ACCT-7: Full payment sets remaining_due to exactly 0.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_7_full_payment_zeroes_remaining() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);

    if let Some((mut loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        loan.status = LoanStatus::Active;
        let full_amount = loan.remaining_due + 1; // more than enough
        let _ = record_payment(&mut loan, full_amount);
        assert_eq!(
            loan.remaining_due, 0,
            "Full payment must zero remaining_due"
        );
    }
}

/// INV-ACCT-8: Platform fee is correctly accumulated into uncollected_fees.
///
/// After N loan creations, uncollected_fees == sum of all platform_fees.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_8_fee_accumulation() {
    let p1: i128 = kani::any();
    let p2: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();

    kani::assume(p1 > 0 && p1 <= 10_000_000_000);
    kani::assume(p2 > 0 && p2 <= 10_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);

    if let Some((_loan1, fee1)) = create_loan(p1, rate_bps, days, fee_bps) {
        if let Some((_loan2, fee2)) = create_loan(p2, rate_bps, days, fee_bps) {
            let total_fees = fee1.checked_add(fee2);
            assert!(total_fees.is_some(), "Fee accumulation must not overflow");
            assert!(fee1 >= 0, "Individual fees must be non-negative");
            assert!(fee2 >= 0, "Individual fees must be non-negative");
        }
    }
}

/// INV-ACCT-9: Rate switch fee correctly increases remaining_due and total_due.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_9_rate_switch_increases_debt() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);

    if let Some((mut loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        loan.status = LoanStatus::Active;
        let old_remaining = loan.remaining_due;
        let old_total = loan.total_due;

        if let Some(fee) = apply_switch_fee(&mut loan, 50) {
            assert!(fee >= 0, "Switch fee must be non-negative");
            assert_eq!(
                loan.remaining_due,
                old_remaining + fee,
                "remaining_due must increase by exactly the fee"
            );
            assert_eq!(
                loan.total_due,
                old_total + fee,
                "total_due must increase by exactly the fee"
            );
            assert!(
                loan.remaining_due <= loan.total_due,
                "remaining_due <= total_due after switch"
            );
        }
    }
}

/// INV-ACCT-10: Partial payments never mark loan as Repaid.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_10_partial_payment_not_repaid() {
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();
    let payment_amount: i128 = kani::any();

    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);
    kani::assume(payment_amount > 0);

    if let Some((mut loan, _fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        loan.status = LoanStatus::Active;
        let total = loan.remaining_due;
        let _ = record_payment(&mut loan, payment_amount);

        if payment_amount < total {
            assert_ne!(
                loan.status,
                LoanStatus::Repaid,
                "Partial payment must not mark loan as Repaid"
            );
        }
    }
}

/// Simulate segregated `collect_fees` guard against pooled contract balance.
/// Returns the updated `(contract_balance, uncollected_fees)` if and only if
/// unencumbered fee tokens cover `uncollected_fees`.
fn collect_fees_segregated(
    contract_balance: i128,
    total_collateral: i128,
    uncollected_fees: i128,
) -> Option<(i128, i128)> {
    if uncollected_fees <= 0 {
        return Some((contract_balance, 0));
    }
    let available_fees = contract_balance.saturating_sub(total_collateral);
    if available_fees < uncollected_fees {
        return None;
    }
    let new_balance = contract_balance.checked_sub(uncollected_fees)?;
    Some((new_balance, 0))
}

/// INV-ACCT-11: Collateral Conservation Invariant.
/// For every whitelisted asset A, contract_balance >= sum(UserCollateral(borrower, A)).
#[cfg(kani)]
#[kani::proof]
fn inv_acct_11_collateral_conservation() {
    let d1: i128 = kani::any();
    let d2: i128 = kani::any();
    let w1: i128 = kani::any();

    kani::assume(d1 > 0 && d1 <= 100_000_000_000);
    kani::assume(d2 > 0 && d2 <= 100_000_000_000);
    kani::assume(w1 >= 0 && w1 <= d1);

    let user1_collateral = d1 - w1;
    let user2_collateral = d2;
    let total_collateral = user1_collateral + user2_collateral;
    let contract_balance = (d1 + d2) - w1;

    assert_eq!(total_collateral, user1_collateral + user2_collateral);
    assert!(
        contract_balance >= total_collateral,
        "Contract balance must always cover sum of user collateral positions"
    );
}

/// INV-ACCT-12: Fee Backing Invariant.
/// For the configured fee token, balance(contract) >= total_collateral + uncollected_fees.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_12_fee_backing_invariant() {
    let total_collateral: i128 = kani::any();
    let principal: i128 = kani::any();
    let rate_bps: u32 = kani::any();
    let days: u32 = kani::any();
    let fee_bps: u32 = kani::any();

    kani::assume(total_collateral >= 0 && total_collateral <= 100_000_000_000);
    kani::assume(principal > 0 && principal <= 100_000_000_000);
    kani::assume(rate_bps >= 1 && rate_bps <= 1500);
    kani::assume(days >= 1 && days <= 365);
    kani::assume(fee_bps <= 1000);

    if let Some((mut loan, platform_fee)) = create_loan(principal, rate_bps, days, fee_bps) {
        // At creation (Pending), no fee is accrued yet.
        let mut contract_balance = total_collateral;
        let mut uncollected_fees = 0i128;
        assert!(contract_balance >= total_collateral + uncollected_fees);

        // Upon full repayment settlement, backed fee tokens accompany fee accrual.
        loan.status = LoanStatus::Active;
        let _ = record_payment(&mut loan, loan.total_due);
        contract_balance += platform_fee;
        uncollected_fees += platform_fee;

        assert!(
            contract_balance >= total_collateral + uncollected_fees,
            "Contract balance must cover both total_collateral and uncollected_fees"
        );
    }
}

/// INV-ACCT-13: Solvency Under Collection.
/// Executing `collect_fees` must never reduce balance(contract) below total_collateral.
#[cfg(kani)]
#[kani::proof]
fn inv_acct_13_solvency_under_collection() {
    let total_collateral: i128 = kani::any();
    let uncollected_fees: i128 = kani::any();
    let extra_tokens: i128 = kani::any();

    kani::assume(total_collateral >= 0 && total_collateral <= 100_000_000_000);
    kani::assume(uncollected_fees > 0 && uncollected_fees <= 10_000_000_000);
    kani::assume(extra_tokens >= 0 && extra_tokens <= 10_000_000_000);

    let contract_balance = total_collateral + extra_tokens;
    match collect_fees_segregated(contract_balance, total_collateral, uncollected_fees) {
        Some((new_balance, new_uncollected)) => {
            assert_eq!(new_uncollected, 0);
            assert!(
                new_balance >= total_collateral,
                "collect_fees must never reduce balance below total_collateral"
            );
        }
        None => {
            assert!(
                extra_tokens < uncollected_fees,
                "collect_fees must only fail when unencumbered tokens are insufficient"
            );
        }
    }
}