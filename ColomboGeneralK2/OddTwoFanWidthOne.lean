import ColomboGeneralK2.OddTwoFanWindows

/-!
# Width one for large two-fan seam windows

For a supported seam window of order at least `m`, the possible row starts
form an interval of width at most one.  The load-bearing combinatorial input
is the Dyck adjacency inequality: the `a`th left event occurs no later than
one position after the preceding right event.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

/-- In a labelled Dyck merge, every noninitial left event occurs no later
than one rank after the preceding right event. -/
theorem TwoFanData.alpha_le_beta_pred_add_one {m : Nat} (D : TwoFanData m)
    (a : Nat) (ha : 0 < a) (ham : a < m) :
    (D.alpha ⟨a, ham⟩ : Nat) ≤
      (D.beta ⟨a - 1, by omega⟩ : Nat) + 1 := by
  by_contra hnot
  have hgap : (D.beta ⟨a - 1, by omega⟩ : Nat) + 1 <
      (D.alpha ⟨a, ham⟩ : Nat) := by omega
  let p : Fin (2 * m) :=
    ⟨(D.beta ⟨a - 1, by omega⟩ : Nat) + 1, by
      have halpha := (D.alpha ⟨a, ham⟩).isLt
      omega⟩
  obtain ⟨q, hq⟩ := D.merge.rank.surjective p
  rcases q with q | q
  · by_cases hqa : (q : Nat) < a
    · have hqpred : q ≤ ⟨a - 1, by omega⟩ := by
        apply Fin.le_iff_val_le_val.mpr
        change (q : Nat) ≤ a - 1
        omega
      have hleft := D.alpha_strictMono.monotone hqpred
      have hpair := D.alpha_lt_beta ⟨a - 1, by omega⟩
      have hlt : (D.alpha q : Nat) < (p : Nat) := by
        change (D.alpha q : Nat) <
          (D.beta ⟨a - 1, by omega⟩ : Nat) + 1
        exact lt_of_le_of_lt hleft (by omega)
      have heq : D.alpha q = p := hq
      apply (ne_of_lt (show D.alpha q < p by exact hlt))
      exact heq
    · have haq : (⟨a, ham⟩ : Fin m) ≤ q := by
        apply Fin.le_iff_val_le_val.mpr
        change a ≤ (q : Nat)
        omega
      have hleft := D.alpha_strictMono.monotone haq
      have heq : D.alpha q = p := hq
      rw [heq] at hleft
      exact (not_lt_of_ge hleft)
        (show p < D.alpha ⟨a, ham⟩ by exact hgap)
  · by_cases hqa : (q : Nat) < a
    · have hqpred : q ≤ ⟨a - 1, by omega⟩ := by
        apply Fin.le_iff_val_le_val.mpr
        change (q : Nat) ≤ a - 1
        omega
      have hright := D.beta_strictMono.monotone hqpred
      have heq : D.beta q = p := hq
      rw [heq] at hright
      change (D.beta ⟨a - 1, by omega⟩ : Nat) + 1 ≤
        (D.beta ⟨a - 1, by omega⟩ : Nat) at hright
      omega
    · have haq : (⟨a, ham⟩ : Fin m) ≤ q := by
        apply Fin.le_iff_val_le_val.mpr
        change a ≤ (q : Nat)
        omega
      have hleft := D.alpha_strictMono.monotone haq
      have hpair := D.alpha_lt_beta q
      have heq : D.beta q = p := hq
      rw [heq] at hpair
      have : (D.alpha ⟨a, ham⟩ : Nat) < (p : Nat) :=
        lt_of_le_of_lt hleft hpair
      exact (not_lt_of_ge hgap.le) this

namespace FanMinorWindow

variable {m : Nat} {D : TwoFanData m}

/-- A seam window of order at least `m` has support interval of width at
most one.  In zero-based notation this is `upper ≤ lower + 1`. -/
theorem large_seam_width_one (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) (hq : m ≤ W.q) :
    W.upper hell ≤ W.lower hb + 1 := by
  let a : Fin m := W.firstLeft hell
  let h : Fin m := W.lastRight hb
  have ha_val : (a : Nat) = m - W.ell := by
    simp [a, firstLeft]
  have hh_val : (h : Nat) = W.c + W.b - 1 := by
    simp [h, lastRight]
  have hell_le := W.ell_le
  have hcb := W.cb_le
  have hbeta_floor := beta_succ_le (D := D) h
  have hq_bound : W.q ≤ m + (D.beta h : Nat) := by
    unfold q
    omega
  by_cases ha0 : (a : Nat) = 0
  · have ha_eq : a = ⟨0, by have hm := D.hm; omega⟩ := by
      apply Fin.ext
      exact ha0
    unfold upper lower
    change (D.alpha a : Nat) ≤
      (m + (D.beta h : Nat) - W.q) + 1
    rw [ha_eq]
    rw [D.alpha_zero]
    exact Nat.zero_le _
  · have ha_pos : 0 < (a : Nat) := Nat.pos_of_ne_zero ha0
    have ha_lt : (a : Nat) < m := a.isLt
    let ap : Fin m := ⟨(a : Nat) - 1, by omega⟩
    have hadj := D.alpha_le_beta_pred_add_one (a : Nat) ha_pos ha_lt
    have hadj' : (D.alpha a : Nat) ≤ (D.beta ap : Nat) + 1 := by
      simpa [ap] using hadj
    have hb_ge_a : (a : Nat) ≤ W.b := by
      unfold q at hq
      omega
    have hap_le_h : ap ≤ h := by
      apply Fin.le_iff_val_le_val.mpr
      dsimp [ap]
      omega
    have hbeta_mono : (D.beta ap : Nat) ≤ (D.beta h : Nat) :=
      D.beta_strictMono.monotone hap_le_h
    have hbeta_growth : (D.beta ap : Nat) +
        ((h : Nat) - (ap : Nat)) ≤ (D.beta h : Nat) := by
      have hdist : (ap : Nat) + ((h : Nat) - (ap : Nat)) < m := by
        rw [Nat.add_sub_of_le (Fin.le_iff_val_le_val.mp hap_le_h)]
        exact h.isLt
      simpa [Nat.add_sub_of_le (Fin.le_iff_val_le_val.mp hap_le_h)] using
        strictMono_fin_add_le D.beta D.beta_strictMono ap
          ((h : Nat) - (ap : Nat)) hdist
    have hap_val : (ap : Nat) = (a : Nat) - 1 := rfl
    have hdist_val : (h : Nat) - (ap : Nat) =
        W.c + W.b - (a : Nat) := by
      omega
    rw [hdist_val] at hbeta_growth
    unfold upper lower
    change (D.alpha a : Nat) ≤
      (m + (D.beta h : Nat) - W.q) + 1
    unfold q at hq_bound ⊢
    omega

end FanMinorWindow

end

end ColomboGeneralK2.Odd
