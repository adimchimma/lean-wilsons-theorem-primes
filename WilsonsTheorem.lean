import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Basic

import Mathlib.Data.Int.ModEq

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Int

import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat


def prime_gen (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  let r : ℕ := Nat.factorial (n - 1) % n
  let q : ℚ := (r : ℚ) / (n - 1)
  (Nat.floor q) * (n - 1) + 2

open Int

-- If we're working mod p, the only numbers that are their
-- own inverses are ± 1
lemma A {p : ℕ} (hp : p.Prime) (x : ℤ) :
  x ^ (2 : ℕ) ≡ 1 [ZMOD p] →
  x ≡ -1 [ZMOD p] ∨ x ≡ 1 [ZMOD p] := by
  intro h
  have hdivide : (p : ℤ) ∣ x ^ (2 : ℕ) - 1 := by
    rw [Int.modEq_iff_dvd] at h
    apply dvd_neg.mp
    ring_nf
    exact h
  -- p | (x + 1) (x - 1)
  have hfactor : (p : ℤ) ∣ (x + 1) * (x - 1) := by
    ring_nf
    rw [add_comm]
    rw [Int.add_neg_one]
    exact hdivide
  clear hdivide
  -- since prime p, p | x + 1 or p | x - 1
  have hprime : (p : ℤ) ∣ x + 1 ∨ (p : ℤ) ∣ x - 1 := by
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact hp'.dvd_or_dvd hfactor
  cases hprime with
  | inl hplus1 =>
      left
      rw [Int.modEq_iff_dvd]
      have heq : (-1) - x = -(1 + x) := by ring
      rw [heq, dvd_neg]
      rw [add_comm]
      exact hplus1
  | inr hminus1 =>
      right
      rw [Int.modEq_iff_dvd]
      have heq : 1 - x = -(x - 1) := by ring
      rw [heq, dvd_neg]
      exact hminus1

lemma B {p : ℕ} (hp : p.Prime) : (p - 1) ≡ -1 [ZMOD p] := by
  rw [Int.modEq_iff_dvd]
  have Hsubcancel : (p : ℤ) ∣ -1 - (p - 1) ↔ (p : ℤ) ∣ -p := by
    ring_nf
  rw [Hsubcancel]
  use (-1)
  ring

-- [⇒]
--    unfold factorial definition
--    by lemma B, p - 1 ≡ -1 [ZMOD p]
--    by lemma A, (p - 1) and 1 are the only numbers that are their own inverses (mod p)
--    This means that everything in between can be written as inverse pairs
--    This leaves us with (p - 1) (mod p) ≡ -1 (mod p)

theorem Wilson (n : ℕ) : Nat.Prime n ↔ ((Nat.factorial (n - 1)) ≡ -1 [ZMOD n]) := by
  apply Iff.intro

  intro Hprime
  have h : n - 1 ≡ -1 [ZMOD n] := B Hprime

  have Hreduce : (Nat.factorial (n - 1)) ≡ (n - 1) [ZMOD n] := by
    have : n - 1 = n - 2 + 1 := by
      cases n with
      | zero => contradiction
      | succ n =>
          cases n with
          | zero => contradiction
          | succ k => simp
    rw [this]
    rewrite [Nat.factorial_succ]

    have HinversePairs : (n - 2).factorial ≡ 1 [ZMOD n] := by
      rewrite [Int.ModEq]
      trans 1

      -- ⊢ ↑(n - 2).factorial % ↑n = 1
      haveI hFact : Fact (Nat.Prime n) := ⟨Hprime⟩

      -- Setup: the "middle" set S = {2, ..., n-2} and the inversion map
      let S : Finset ℕ := Finset.Icc 2 (n - 2)
      let inv : ℕ → ℕ := fun a => ((a : ZMod n)⁻¹).val

      -- [1] Inversion sends S into S
      --     (if 2 ≤ a ≤ n-2, then a⁻¹ mod n is also in {2,...,n-2})
      have inv_mem : ∀ a ∈ S, inv a ∈ S := by
        intro a HainS
        -- Setup: extract a's bounds and standard facts about n
        have hn2 : 2 ≤ n := Hprime.two_le
        haveI : NeZero n := ⟨by omega⟩
        haveI : Fact (1 < n) := ⟨by omega⟩
        rw [show S = Finset.Icc 2 (n - 2) from rfl, Finset.mem_Icc] at HainS
        obtain ⟨ha_lo, ha_hi⟩ := HainS
        have ha_lt_n : a < n := by omega

        -- (a : ZMod n) is a unit (i.e. nonzero), since 0 < a < n
        have ha_ne_zero : (a : ZMod n) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd
          have : n ≤ a := Nat.le_of_dvd (by omega) hdvd
          omega

        -- The cast of (n-1 : ℕ) into ZMod n is -1; we'll use this twice
        have hcast_nm1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
          have h1 : (1 : ℕ) ≤ n := by omega
          rw [Nat.cast_sub h1, Nat.cast_one, ZMod.natCast_self, zero_sub]

        -- Let b := inv a; we show 2 ≤ b ≤ n-2 by ruling out b = 0, 1, n-1
        show inv a ∈ Finset.Icc 2 (n - 2)
        rw [Finset.mem_Icc]
        set b : ℕ := inv a with hb_def
        have hb_lt_n : b < n := ZMod.val_lt _

        -- The defining property: ((b : ℕ) : ZMod n) = (a : ZMod n)⁻¹
        have hb_cast : ((b : ℕ) : ZMod n) = (a : ZMod n)⁻¹ := by
          show (((a : ZMod n)⁻¹).val : ZMod n) = (a : ZMod n)⁻¹
          exact ZMod.natCast_zmod_val _

        -- b ≠ 0, since (a : ZMod n)⁻¹ ≠ 0
        have hb_ne_0 : b ≠ 0 := by
          show ((a : ZMod n)⁻¹).val ≠ 0
          rw [Ne, ZMod.val_eq_zero]
          exact inv_ne_zero ha_ne_zero

        -- (a : ZMod n) ≠ 1: else a = 1 in ℕ, contradicting a ≥ 2
        have ha_ne_one : (a : ZMod n) ≠ 1 := by
          intro h
          have hval : ((a : ZMod n)).val = (1 : ZMod n).val := by rw [h]
          simp only [ZMod.val_natCast_of_lt ha_lt_n, ZMod.val_one] at hval
          omega

        -- b ≠ 1: if b = 1 then (a : ZMod n)⁻¹ = 1, hence (a : ZMod n) = 1
        have hb_ne_1 : b ≠ 1 := by
          intro h
          apply ha_ne_one
          have : (a : ZMod n)⁻¹ = 1 := by
            have hcast_one : ((b : ℕ) : ZMod n) = 1 := by rw [h]; push_cast; rfl
            rw [hb_cast] at hcast_one
            exact hcast_one
          exact (inv_eq_one.mp this)

        -- (a : ZMod n) ≠ -1: else a = n-1, contradicting a ≤ n-2
        have ha_ne_neg_one : (a : ZMod n) ≠ -1 := by
          intro h
          rw [← hcast_nm1] at h
          have hval : ((a : ZMod n)).val = ((n - 1 : ℕ) : ZMod n).val := by rw [h]
          simp only [ZMod.val_natCast_of_lt ha_lt_n,
                     ZMod.val_natCast_of_lt (by omega : n - 1 < n)] at hval
          omega

        -- b ≠ n-1: if b = n-1 then (a : ZMod n)⁻¹ = -1, hence (a : ZMod n) = -1
        have hb_ne_nm1 : b ≠ n - 1 := by
          intro h
          apply ha_ne_neg_one
          have : (a : ZMod n)⁻¹ = -1 := by
            have hcast_neg : ((b : ℕ) : ZMod n) = -1 := by rw [h]; exact hcast_nm1
            rw [hb_cast] at hcast_neg
            exact hcast_neg
          rw [eq_neg_iff_add_eq_zero, ← eq_neg_iff_add_eq_zero] at this ⊢
          rw [← inv_inj, this, inv_neg, inv_one]

        -- Combine: 0 < b < n, b ≠ 1, b ≠ n-1  ⟹  2 ≤ b ≤ n-2
        refine ⟨?_, ?_⟩ <;> omega



      -- [2] Inversion is an involution on S
      --     ((a⁻¹)⁻¹ = a in ZMod n, then take .val)
      have inv_inv : ∀ a ∈ S, inv (inv a) = a := by
        sorry

      -- [3] Inversion has no fixed points on S
      --     (by Lemma A, a = a⁻¹ forces a ≡ ±1, neither of which lies in S)
      have inv_ne : ∀ a ∈ S, inv a ≠ a := by
        sorry

      -- [4] Pair every a ∈ S with inv a; T picks the "smaller half" of each pair
      let T : Finset ℕ := S.filter (fun a => a < inv a)

      -- [5] S decomposes as T ⊎ inv(T)
      have hT_union : S = T ∪ T.image inv := by
        sorry
      -- [5.] T and inv T are disjoint
      have hT_disjoint : Disjoint T (T.image inv) := by
        sorry

      -- [6] In ZMod n, product over S splits over the pairing and each pair gives 1
      --     ∏_{a ∈ S} a = ∏_{a ∈ T} a · ∏_{a ∈ T} inv a = ∏_{a ∈ T} (a · a⁻¹) = 1
      have h_prod_S : ∏ i ∈ S, (i : ZMod n) = 1 := by
        sorry

      -- [7] (n-2)! equals the product over S as a natural number
      --     (since S = {2,...,n-2} and 1 contributes a factor of 1)
      have h_fact_eq_prod : (n - 2).factorial = ∏ i ∈ S, i := by
        sorry

      -- [8] Conclude in ZMod n: ((n-2)! : ZMod n) = 1
      have h_cast : ((n - 2).factorial : ZMod n) = 1 := by
        rw [h_fact_eq_prod]
        push_cast
        exact_mod_cast h_prod_S

      -- [9] Cast back to a Nat-level Int.ModEq statement
      sorry


      -- ⊢ 1 = 1 % ↑n
      have Hnnonzero : 1 < n := by
        exact_mod_cast (Nat.Prime.one_lt Hprime)
      rewrite [Int.emod_eq_of_lt]
      rfl
      norm_num
      exact_mod_cast Hnnonzero

    rewrite [← this]
    calc ↑((n - 1) * (Nat.factorial (n - 2)))
        ≡ (n - 1) * 1 [ZMOD n] := sorry
      _ = (n - 1) := by ring_nf
  trans (n - 1)
  exact Hreduce
  exact h

  sorry
