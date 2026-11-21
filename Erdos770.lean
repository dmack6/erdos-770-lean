import Lean

/-!
  An arithmetic reduction for Erdős Problem 770(iii), checked with Lean 4.19.0.

  The inputs to `threshold` are the Fermat congruence, availability of a
  small primitive root, the count of products of small primes, and the
  root bound over a prime field. See the companion paper for these inputs
  and the passage from Dirichlet GRH to the eventual threshold.
-/

namespace Erdos770Reduction

def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, 2 ≤ d → d < p → ¬ d ∣ p

/-- The collective gcd through the cutoff, with zero as the empty gcd. -/
def collectiveGcd (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 =>
    if m = 0 then 0 else Nat.gcd (collectiveGcd n m) ((m + 1) ^ n - 1)

theorem dvd_collectiveGcd {n m r : Nat} :
    r ∣ collectiveGcd n m ↔ ∀ a : Nat, 2 ≤ a → a ≤ m → r ∣ a ^ n - 1 := by
  induction m with
  | zero => simp [collectiveGcd]; omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      simp [collectiveGcd]; omega
    · rw [collectiveGcd, if_neg hm]
      constructor
      · intro hd a ha ham
        by_cases heq : a = m + 1
        · subst a
          exact Nat.dvd_trans hd (Nat.gcd_dvd_right _ _)
        · exact ih.mp (Nat.dvd_trans hd (Nat.gcd_dvd_left _ _)) a ha (by omega)
      · intro hall
        exact Nat.dvd_gcd (ih.mpr fun a ha ham => hall a ha (by omega))
          (hall (m + 1) (by omega) (by omega))

private theorem exists_prime_divisor (g : Nat) (hg : 2 ≤ g) :
    ∃ r, Prime r ∧ r ∣ g := by
  induction g using Nat.strongRecOn with
  | ind g ih =>
    by_cases hd : ∃ d, 2 ≤ d ∧ d < g ∧ d ∣ g
    · obtain ⟨d, hd2, hdg, hdiv⟩ := hd
      obtain ⟨r, hr, hrd⟩ := ih d hdg hd2
      exact ⟨r, hr, Nat.dvd_trans hrd hdiv⟩
    · exact ⟨g, ⟨hg, fun d hd2 hdg hdvd => hd ⟨d, hd2, hdg, hdvd⟩⟩, Nat.dvd_refl g⟩

private theorem root_of_dvd {n a r : Nat} (ha : 0 < a) (hr : 1 < r)
    (h : r ∣ a ^ n - 1) : a ^ n % r = 1 := by
  have hpos : 1 ≤ a ^ n := Nat.pow_pos ha
  calc
    a ^ n % r = (a ^ n - 1 + 1) % r :=
      congrArg (fun b => b % r) (Nat.sub_add_cancel hpos).symm
    _ = 1 := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h, Nat.mod_eq_of_lt hr,
                    Nat.zero_add, Nat.mod_eq_of_lt hr]

private theorem dvd_of_root {n a r : Nat}
    (h : a ^ n % r = 1) : r ∣ a ^ n - 1 := by
  have hdiv := Nat.mod_add_div (a ^ n) r
  rw [h] at hdiv
  exact ⟨a ^ n / r, by omega⟩

private theorem self_not_root {r n : Nat} (hn : 0 < n) :
    r ^ n % r ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
  omega

def listProduct : List Nat → Nat
  | [] => 1
  | a :: tail => a * listProduct tail

private theorem product_is_root {n r p : Nat} (hr : 1 < r)
    (h : ∀ a : Nat, 2 ≤ a → a ≤ p → a ^ n % r = 1) :
    ∀ factors : List Nat, (∀ a ∈ factors, 2 ≤ a ∧ a ≤ p) →
      listProduct factors ^ n % r = 1 := by
  intro factors
  induction factors with
  | nil => simp [listProduct, Nat.mod_eq_of_lt hr]
  | cons a tail ih =>
    intro hall
    have ha := hall a (by simp)
    have ht : ∀ b ∈ tail, 2 ≤ b ∧ b ≤ p := fun b hb => hall b (by simp [hb])
    rw [listProduct, Nat.mul_pow, Nat.mul_mod, h a ha.1 ha.2, ih ht]
    simp [Nat.mod_eq_of_lt hr]

/-- A supply of distinct products representing more than n roots if all their
factors are roots. Each product lies in the range through n². -/
def ManyProducts (n p : Nat) : Prop :=
  ∃ products : List (List Nat),
    n < products.length ∧ (products.map listProduct).Nodup ∧
    ∀ factors ∈ products,
      (∀ a ∈ factors, 2 ≤ a ∧ a ≤ p) ∧ listProduct factors ≤ n ^ 2

/-- The root bound for X^n - 1, stated for lists of distinct representatives. -/
def PrimeFieldRootBound : Prop :=
  ∀ r n : Nat, Prime r → 0 < n →
    ∀ roots : List Nat, roots.Nodup →
      (∀ a ∈ roots, a < r ∧ a ^ n % r = 1) → roots.length ≤ n

/-- For primes in the middle range, a generator can be chosen below the cutoff. -/
def SmallGenerators (n p : Nat) : Prop :=
  ∀ r : Nat, Prime r → p < r → r ≤ n ^ 2 →
    ∃ q : Nat, 2 ≤ q ∧ q ≤ p ∧
      ∀ e : Nat, q ^ e % r = 1 ↔ r - 1 ∣ e

/-- The first cutoff at which the collective gcd is one. -/
def FirstCutoff (n p : Nat) : Prop :=
  2 ≤ p ∧ collectiveGcd n p = 1 ∧
    ∀ m : Nat, 2 ≤ m → m < p → collectiveGcd n m ≠ 1

theorem threshold {n p : Nat} (hn : 0 < n) (hp : Prime p)
    (hpdiv : p - 1 ∣ n)
    (hmax : ∀ r : Nat, Prime r → r - 1 ∣ n → r ≤ p)
    (fermat : ∀ a : Nat, 2 ≤ a → a < p → a ^ (p - 1) % p = 1)
    (generators : SmallGenerators n p)
    (products : ManyProducts n p)
    (rootBound : PrimeFieldRootBound) :
    FirstCutoff n p := by
  have hp1 : 1 < p := hp.1
  refine ⟨hp.1, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hg
    have hnonzero : collectiveGcd n p ≠ 0 := by
      intro hzero
      have ha := (dvd_collectiveGcd (n := n) (m := p) (r := 0)).mp
        (by simp [hzero]) p hp.1 (Nat.le_refl p)
      have hz : p ^ n - 1 = 0 := by simpa using ha
      have he : p ^ n = 1 := by have := Nat.pow_pos (a := p) (n := n) (by omega); omega
      exact self_not_root hn (r := p) (by rw [he, Nat.mod_eq_of_lt hp1])
    obtain ⟨r, hr, hd⟩ := exists_prime_divisor (collectiveGcd n p) (by omega)
    have hr1 : 1 < r := hr.1
    have hall := (dvd_collectiveGcd (n := n) (m := p)).mp hd
    have hroots : ∀ a : Nat, 2 ≤ a → a ≤ p → a ^ n % r = 1 :=
      fun a ha hap => root_of_dvd (n := n) (a := a) (by omega) hr1 (hall a ha hap)
    have hrp : p < r := by
      apply Classical.byContradiction
      intro hle
      exact self_not_root hn (hroots r hr.1 (by omega))
    by_cases hmedium : r ≤ n ^ 2
    · obtain ⟨q, hq2, hqp, horder⟩ := generators r hr hrp hmedium
      exact (Nat.not_le_of_lt hrp) (hmax r hr ((horder n).mp (hroots q hq2 hqp)))
    · obtain ⟨lists, hcount, hdistinct, hfac⟩ := products
      have hbound := rootBound r n hr hn (lists.map listProduct) hdistinct (by
        intro a ham
        obtain ⟨factors, hmem, rfl⟩ := List.mem_map.mp ham
        obtain ⟨hsmall, hprod⟩ := hfac factors hmem
        exact ⟨by omega, product_is_root hr1 hroots factors hsmall⟩)
      rw [List.length_map] at hbound
      omega
  · intro m _ hmp heq
    have hdiv : p ∣ collectiveGcd n m := dvd_collectiveGcd.mpr (by
      intro a ha ham
      have hfermat := fermat a ha (by omega)
      obtain ⟨t, ht⟩ := hpdiv
      apply dvd_of_root
      rw [ht, Nat.pow_mul]
      clear ht
      induction t with
      | zero => simp [Nat.mod_eq_of_lt hp1]
      | succ t ih =>
        rw [Nat.pow_succ, Nat.mul_mod, ih, hfermat]
        simp [Nat.mod_eq_of_lt hp1])
    rw [heq, Nat.dvd_one] at hdiv
    omega

#print axioms threshold

end Erdos770Reduction
