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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Order.Interval.Finset.Nat


def primeGenerator (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  let r : ℕ := Nat.factorial (n - 1) % n
  let q : ℚ := (r : ℚ) / (n - 1)
  (Nat.floor q) * (n - 2) + 2

open Int

-- If we're working mod p, the only numbers that are their
-- own inverses are ± 1
lemma A {p : ℕ} (hp : p.Prime) (x : ℤ) :
    x ^ (2 : ℕ) ≡ 1 [ZMOD p] →
    x ≡ -1 [ZMOD p] ∨ x ≡ 1 [ZMOD p] := by
  intro H
  have Hdivides : (p : ℤ) ∣ x ^ (2 : ℕ) - 1 := by
    rw [Int.modEq_iff_dvd] at H
    apply dvd_neg.mp
    ring_nf
    exact H

  have Hfactored : (p : ℤ) ∣ (x + 1) * (x - 1) := by
    ring_nf
    rw [add_comm]
    rw [Int.add_neg_one]
    exact Hdivides

  clear Hdivides

  -- since prime p, p | x + 1 or p | x - 1
  have Hprime : (p : ℤ) ∣ x + 1 ∨ (p : ℤ) ∣ x - 1 := by
    have : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact this.dvd_or_dvd Hfactored

  cases Hprime with
  | inl Hplus₁ =>
      left
      rw [Int.modEq_iff_dvd]
      have heq : (-1) - x = -(1 + x) := by ring
      rw [heq, dvd_neg]
      rw [add_comm]
      exact Hplus₁
  | inr Hminus₁ =>
      right
      rw [Int.modEq_iff_dvd]
      have heq : 1 - x = -(x - 1) := by ring
      rw [heq, dvd_neg]
      exact Hminus₁


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
-- [⇐]
--    procede by contraposition
--    consider the case when n = 4; closes by computation
--    consider the case when n = p² for prime p;
--       (n - 1)! = (p² - 1)!
--                = (p² - 1)(p² - 2) ⋯ (2p) ⋯ (p) ⋯ 3·2·1
--          we know 2p and p are in the product because
--              for p ≥ 3, p² - 1 ≥ 3² - 1 = 8 > 2p ≥ 2(3) = 6 > 3
--                = 2p² · ∏ i ∈ Finset.Icc 1 (p² - 1) \ {p, 2p}, i
--                ≡ 0 [ZMOD p²]
--    similarly, consider the case when n = a*b for 1 < a < b < n;
--       (n - 1)! = (n - 1) ⋯ (b) ⋯ (a) ⋯ 3·2·1
--                = (a * b) · ∏ i ∈ Finset.Icc 1 (n - 1) \ {a, b}, i
--                = 0 [ZMOD n]
--     In all cases, we do not get -1 [ZMOD n] as required

theorem Wilson (p : ℕ) (hp : 1 < p) : Nat.Prime p ↔ ((Nat.factorial (p - 1)) ≡ -1 [ZMOD p]) := by
  apply Iff.intro
  · intro Hprime
    have HB : p - 1 ≡ -1 [ZMOD p] := B Hprime

    have Hreduce : (Nat.factorial (p - 1)) ≡ (p - 1) [ZMOD p] := by
      have : p - 1 = p - 2 + 1 := by
        cases p with
        | zero => contradiction
        | succ n =>
            cases n with
            | zero => contradiction
            | succ k => simp
      rw [this]
      rewrite [Nat.factorial_succ]
      rw [<- this]
      clear this

      have HinversePairs : (p - 2).factorial ≡ 1 [ZMOD p] := by
        -- A lot of the machinery around ZMod p being a Field, (or technically strictly smaller structure)
        --    relies on the fact that p is prime (as is true on pen and paper)
        --    However, all of that is wired through typeclass instances and not explicitly,
        --    so register Nat.Prime p as a typeclass (using the constructor `Fact`) makes it available to
        --    the elaborator
        haveI hFact : Fact (Nat.Prime p) := ⟨Hprime⟩

        -- Setup: the middle set S = {2, ..., n-2} and the inversion map
        let S : Finset ℕ := Finset.Icc 2 (p - 2)
        let inv : ℕ → ℕ := fun a => ((a : ZMod p)⁻¹).val


        have Hunfold : (p - 2).factorial = ∏ i ∈ S, i := by
          rw [show S = Finset.Icc 2 (p - 2) from rfl]

          rw [← Finset.prod_Ico_id_eq_factorial]
          rw [← Order.succ_eq_add_one]
          rw [Finset.Ico_succ_right_eq_Icc 1 (p - 2)]

          rcases Nat.eq_zero_or_pos (p - 2) with h | h
          · simp [h]
          · have hset : Finset.Icc 1 (p - 2) = insert 1 (Finset.Icc 2 (p - 2)) := by
              ext x
              simp only [Finset.mem_Icc, Finset.mem_insert]
              omega
            rw [hset]
            rw [Finset.prod_insert (by simp)]
            simp

        rw [Hunfold]

        have Hinv_mem : ∀ n ∈ S, inv n ∈ S := by
          intro n Hin
          rw [show S = Finset.Icc 2 (p - 2) from rfl]
          rw [Finset.mem_Icc]

          have Hneq_lower : inv n ≠ 0 ∧ inv n ≠ 1 := by
            apply And.intro
            · rw [Ne, ZMod.val_eq_zero]
              apply inv_ne_zero

              rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
              rw [Finset.mem_Icc] at Hin
              obtain ⟨Hge, Hle⟩ := Hin
              rw [Ne, ZMod.natCast_eq_zero_iff]
              intro Hdivide
              have : p ≤ n := Nat.le_of_dvd (by omega) Hdivide
              omega
            · -- inv n ≠ 1 case.
              -- if n⁻¹ is 1 then n must be 1 [inverses are unique, 1 is always its inverse].
              -- this implies that n ∉ S, however this results in a contradiction as we've assumed n ∈ S @Hinv_mem
              intro Hcontradiction
              unfold inv at Hcontradiction

              have : (n : ZMod p)⁻¹ = 1 := by
                rw [← ZMod.natCast_zmod_val ((n : ZMod p)⁻¹), Hcontradiction, Nat.cast_one]

              have Heq_one : (n : ZMod p) = 1 := inv_eq_one.mp this
              have : (n : ZMod p).val = (1 : ZMod p).val := by rw [Heq_one]

              rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
              rw [Finset.mem_Icc] at Hin
              obtain ⟨Hge, _⟩ := Hin

              rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_one] at this
              omega

          have Hloose_upper_bound : inv n < p := ZMod.val_lt _

          have Hneq : inv n ≠ p - 1 := by
            unfold inv
            intro Hcontradiction

            have Hmod_reduce : ((p - 1 : ℕ) : ZMod p) = -1 := by
              rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ p)]
              rw [Nat.cast_one, ZMod.natCast_self, zero_sub]

            have : (n : ZMod p)⁻¹ = -1 := by
              rw [← ZMod.natCast_zmod_val ((n : ZMod p)⁻¹), Hcontradiction]
              rw [Hmod_reduce]

            have Heq : (n : ZMod p) = -1 := by
              have h := congrArg (·⁻¹) this
              simpa using h

            rw [← Hmod_reduce] at Heq
            have : (n : ZMod p).val = ((p - 1 : ℕ) : ZMod p).val := by rw [Heq]

            rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
            rw [Finset.mem_Icc] at Hin

            rw [ZMod.val_natCast_of_lt (by omega : n < p)] at this
            rw [ZMod.val_natCast_of_lt (by omega : p - 1 < p)] at this
            omega

          omega


        have Hneq_inv : ∀ n ∈ S, n ≠ inv n := by
          intros n Hin
          intro Hcontradiction

          have Hinv : (n : ZMod p) * inv n = 1 := by
            unfold inv
            simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
            apply mul_inv_cancel₀

            rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
            rw [Finset.mem_Icc] at Hin
            obtain ⟨Hge, Hle⟩ := Hin

            intro Heq

            rw [ZMod.natCast_eq_zero_iff] at Heq
            have : p ≤ n := Nat.le_of_dvd (by omega) Heq
            omega

          rw [← Hcontradiction] at Hinv
          rw [← pow_two] at Hinv

          have : (n : ℤ) ^ (2 : ℕ) ≡ 1 [ZMOD p] := by
            rw [← ZMod.intCast_eq_intCast_iff]
            exact_mod_cast Hinv

          apply (A Hprime) at this
          cases this with
          | inl Hneg =>
              rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
              rw [Finset.mem_Icc] at Hin
              obtain ⟨Hge, Hle⟩ := Hin

              rw [Int.modEq_iff_dvd] at Hneg
              have Hdivide : (p : ℤ) ∣ (n : ℤ) + 1 := by
                rwa [show (-1 : ℤ) - (n : ℤ) = -((n : ℤ) + 1) from by ring, dvd_neg] at Hneg

              have hle := Int.le_of_dvd (by omega) Hdivide
              omega
          | inr Hpos =>
              rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
              rw [Finset.mem_Icc] at Hin
              obtain ⟨Hge, Hle⟩ := Hin

              rw [Int.modEq_iff_dvd] at Hpos
              have Hdivide : (p : ℤ) ∣ (n : ℤ) - 1 := by
                rwa [show (1 : ℤ) - (n : ℤ) = -((n : ℤ) - 1) from by ring, dvd_neg] at Hpos

              have hle := Int.le_of_dvd (by omega) Hdivide
              omega


        have Hinv_inv : ∀ n ∈ S, inv (inv n) = n := by
          intro n Hin
          unfold inv
          rw [ZMod.natCast_zmod_val]
          rw [inv_inv]
          rw [ZMod.val_natCast_of_lt]

          rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
          rw [Finset.mem_Icc] at Hin
          obtain ⟨_, Hle⟩ := Hin
          omega


        have Hinv_prop : ∀ n ∈ S, (n : ZMod p) * (inv n : ZMod p) = 1 := by
          intro n Hin
          unfold inv
          rw [ZMod.natCast_zmod_val]
          -- Defined over integral domains: mul_inv_cancel₀.{u} {G₀ : Type u} [GroupWithZero G₀] {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1
          apply mul_inv_cancel₀

          -- The proof obligation is then to prove (n : ZMod) ≠ 0
          -- First define the bounds on (n : ℕ)
          rw [show S = Finset.Icc 2 (p - 2) from rfl] at Hin
          rw [Finset.mem_Icc] at Hin
          obtain ⟨_, Hle⟩ := Hin

          -- We know (n : ZMod p) ≠ 0 ↔ p ∤ (n : ℕ)
          rw [Ne, ZMod.natCast_eq_zero_iff]
          -- So by way of contradiction, Assume p | (n : ℕ)
          -- This implies p ≤ n, but this contradicts Hle the upper bound [n ≤ p - 2]
          intro Hdivides
          have : p ≤ n := Nat.le_of_dvd (by omega) Hdivides
          omega


        -- For each element t, we can extract t and t⁻¹ from the product
        -- We know that we can do this because every element has an inverse in the set
        -- Also the inverse is involutive, so we always get a pair and not a chain
        -- We also know that no element is its own inverse so it must have an element to multiply with
        -- Thus, we always have two arbitrary elements t and t⁻¹ with (t * t⁻¹) = 1
        -- Because we can deconstruct the set S like this ∏ i ∈ S, i must equal 1
        -- We prove this with strong induction by showing the above properties continue to hold
        --    for S \ {t, t⁻¹}
        have H : ∀ T : Finset ℕ,
            (∀ t ∈ T, inv t ∈ T) →
            (∀ t ∈ T, t ≠ inv t) →
            (∀ t ∈ T, inv (inv t) = t) →
            (∀ t ∈ T, (t : ZMod p) * (inv t : ZMod p) = 1) →
            ∏ i ∈ T, (i : ZMod p) = 1 := by
          intro T
          induction T using Finset.strongInduction with
          | H T IH =>
            intros Hclosed Hnofixpoints Hinvolutive Hinverse
            rcases T.eq_empty_or_nonempty with rfl | ⟨n, Hin⟩
            · simp
            · let T₁ := T \ {n, inv n}

              have Hpair_subset : {n, inv n} ⊆ T := by
                intro s Hs
                simp only [Finset.mem_insert, Finset.mem_singleton] at Hs
                rcases Hs with rfl | rfl
                · exact Hin
                · exact (Hclosed n Hin)

              have Hsubset : T₁ ⊂ T := Finset.sdiff_ssubset Hpair_subset (by simp)

              rw [← Finset.prod_sdiff Hpair_subset]
              rw [Finset.prod_pair (Hnofixpoints n Hin)]
              rw [Hinverse n Hin, mul_one]
              rw [IH T₁ Hsubset ?_ ?_ ?_ ?_]
              · -- ∀ t ∈ T₁, inv t ∈ T₁
                -- The plan is simply to infold T₁ and identify what it means
                --    to be an element of T₁ i.e. t ∈ T₁ ↔ t ∈ T ∧ t ∉ {n, inv n}
                -- We already know that inv t is in T, but we need to show that t is
                --    not in the pair
                intro t Ht
                rw [Finset.mem_sdiff] at Ht ⊢
                obtain ⟨HinT, HninPair⟩ := Ht
                refine ⟨Hclosed t HinT, ?_⟩

                -- We proceed by contradiction
                -- Assume inv t ∈ {n, inv n}
                -- Then t = inv (inv t) ∈ {n, inv n} which contradicts the assumption
                --    that t ∉ {n, inv n}
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at HninPair
                obtain ⟨Hneq, HneqInv⟩ := HninPair
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                refine ⟨?_, ?_⟩
                · intro Hcontradiction
                  apply congrArg inv at Hcontradiction
                  rw [Hinvolutive t HinT] at Hcontradiction
                  omega
                · intro Hcontradiction
                  apply congrArg inv at Hcontradiction
                  repeat rw [Hinvolutive] at Hcontradiction
                  omega
                  · exact Hin
                  · exact HinT
              · -- ∀ t ∈ T₁, t ≠ inv t
                -- We get for free as its a property of T ⊇ T₁
                intro t Ht
                have HinT : t ∈ T := (Finset.mem_sdiff.mp Ht).1
                exact Hnofixpoints t HinT
              · -- ∀ t ∈ T₁, inv (inv t) = t
                -- We get for free as its a property of T ⊇ T₁
                intro t Ht
                have HinT : t ∈ T := (Finset.mem_sdiff.mp Ht).1
                exact Hinvolutive t HinT
              · -- ∀ t ∈ T₁, (t : ZMod p) * ↑(inv t) = 1
                -- We get for free as its a property of T ⊇ T₁
                intro t Ht
                have HinT : t ∈ T := (Finset.mem_sdiff.mp Ht).1
                exact Hinverse t HinT

        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        exact H S Hinv_mem Hneq_inv Hinv_inv Hinv_prop

      push_cast
      calc (↑(p - 1) : ℤ) * ↑(p - 2).factorial
          ≡ ↑(p - 1) * 1 [ZMOD ↑p] := Int.ModEq.mul_left _ HinversePairs
        _ ≡ ↑(p - 1) [ZMOD ↑p] := by rw [mul_one]

      have : 2 ≤ p := Hprime.two_le
      rw [Nat.cast_sub (by omega)]
      apply Int.ModEq.rfl

    calc ↑(p - 1).factorial
        ≡ ↑p - 1 [ZMOD ↑p] := Hreduce
      _ ≡ -1 [ZMOD ↑p] := HB
  · contrapose
    set n := p
    intro Hcomposite
    by_cases! n₄ : n = 4
    · rw [n₄]; decide
    · by_cases! Hp : ∃ p, Nat.Prime p ∧ n = p ^ 2
      · obtain ⟨p, ⟨Hprime, Heq⟩⟩ := Hp
        rw [Heq]

        let S : Finset ℕ := Finset.Icc 1 (p ^ 2 - 1)

        have Hunfold : (p ^ 2 - 1).factorial = ∏ i ∈ S, i := by
          rw [← Finset.prod_Ico_id_eq_factorial]
          rw [← Order.succ_eq_add_one]
          rw [Finset.Ico_succ_right_eq_Icc 1 (p ^ 2 - 1)]

        rw [Hunfold]

        have Hfactor : ∏ i ∈ S, i = 2 * p ^ 2 * ∏ i ∈ S \ {p, 2 * p}, i := by
          have Hsubset : {p , 2 * p} ⊆ S := by
            intros m Hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at Hm

            rw [show S = Finset.Icc 1 (p ^ 2 - 1) from rfl]
            rw [Finset.mem_Icc]

            have Hlowerbound : 2 ≤ p := Hprime.two_le
            have Hle : p < 2 * p := by omega
            have Hupperbound : 2 * p < p ^ 2 - 1 := by
              have Hneq : p ≠ 2 := by
                intro Heq_two
                apply n₄
                rw [Heq, Heq_two]
                simp

              have Hge₃ : 3 ≤ p := by omega

              calc 2 * p
                  < (3 * p) - 1 := by omega -- 2p + (p - 1)
                _ ≤ (p * p) - 1 := by       -- 3 ≤ p
                    apply Nat.sub_le_sub_right
                    nlinarith
                _ = p ^ 2 - 1 := by rw [Nat.pow_two]

            omega

          rw [← Finset.prod_sdiff Hsubset]
          rw [Finset.prod_pair]
          · ring
          · have : 2 ≤ p := Hprime.two_le
            omega

        rw [Hfactor]

        have Hreduce : (2 * p ^ 2 * ∏ i ∈ S \ {p, 2 * p}, i) ≡ 0 [ZMOD ↑(p ^ 2)] := by
          rw [Int.modEq_zero_iff_dvd]
          use (2 * (∏ i ∈ S \ {p, 2 * p}, i))
          push_cast
          ring

        intro Hcontradiction
        have Hrewrite : (0 : ℤ) ≡ -1 [ZMOD (↑(p ^ 2))] := Hreduce.symm.trans Hcontradiction
        rw [Int.modEq_iff_dvd] at Hrewrite

        norm_num at Hrewrite
        have : (p ^ 2 : ℕ) ∣ 1 := by exact_mod_cast Hrewrite

        have : p ^ 2 = 1 := Nat.dvd_one.mp this
        have : 2 ≤ p := Hprime.two_le
        nlinarith
      · have Hconstruction : ∃ a b, (1 < a ∧ a < b ∧ b < n) ∧ n = a * b := by
          use (n.minFac), (n / n.minFac)
          refine ⟨?_, ?_⟩
          · have HminFacPrime : (n.minFac).Prime := Nat.minFac_prime (by omega)
            have : 2 ≤ (n.minFac) := HminFacPrime.two_le
            refine ⟨?_, ?_, ?_⟩
            · omega
            · have Hle : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) Hcomposite
              have Hidentity : n.minFac * (n / n.minFac) = n := by
                rw [Nat.mul_div_cancel_left']
                exact Nat.minFac_dvd n

              have : n.minFac ≠ n / n.minFac := by
                intro Hcontradiction
                apply Hp n.minFac HminFacPrime
                rw [pow_two]
                nth_rewrite 2 [Hcontradiction]
                exact Hidentity.symm

              omega
            · exact Nat.div_lt_self (by omega) (by omega)
          · rw [Nat.mul_div_cancel']
            exact Nat.minFac_dvd n

        let S : Finset ℕ := Finset.Icc 1 (n - 1)
        have Hunfold : (n - 1).factorial = ∏ i ∈ S, i := by
          rw [← Finset.prod_Ico_id_eq_factorial]
          rw [← Order.succ_eq_add_one]
          rw [Finset.Ico_succ_right_eq_Icc 1 (n - 1)]

        rw [Hunfold]

        obtain ⟨a, b, Hbounds, Heq⟩ := Hconstruction
        have Hfactor : ∏ i ∈ S, i = (a * b) * ∏ i ∈ S \ {a, b}, i := by
          have Hsubset : {a, b} ⊆ S := by
            intro m Hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at Hm

            rw [show S = Finset.Icc 1 (n - 1) from rfl]
            rw [Finset.mem_Icc]
            omega

          rw [← Finset.prod_sdiff Hsubset]
          rw [Finset.prod_pair]
          · ring
          · omega

        rw [Hfactor]

        have Hreduce : a * b * ∏ i ∈ S \ {a, b}, i ≡ 0 [ZMOD ↑n] := by
          rw [Int.modEq_zero_iff_dvd]
          rw [Heq]
          use (∏ i ∈ S \ {a, b}, i)
          push_cast
          ring

        intro Hcontradiction
        have Hrewrite : (0 : ℤ) ≡ -1 [ZMOD (↑n)] := Hreduce.symm.trans Hcontradiction
        rw [Int.modEq_iff_dvd] at Hrewrite

        norm_num at Hrewrite
        have : (n : ℕ) ∣ 1 := by exact_mod_cast Hrewrite

        have : n = 1 := Nat.dvd_one.mp this
        nlinarith
