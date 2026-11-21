import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSecMulPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponentsStatement

section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_supLattice_degree_twist_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E) (B : Finset ℕ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ p ∈ B, p.Prime) → IntOff B s.lo → GoodOn U x V dict Z G → degOn U x V dict Z G + (rankOn U Z G : ℝ) * (s.degLo - logSum B) ≤ degOn U x V dict Z (G + G₀) := by
  first | exact @GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le | exact GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le | (intros; apply GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Proof.TwistedWeightDegree

theorem degW_twist : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ (G₀ G : WTZ D.host.E) (s : ∀ Z : Comp Xo c, TwSec U (xiR D) Z G₀) (B : Finset ℕ) (τ : ℝ), Even G.2 → (∀ p ∈ B, p.Prime) → (∀ Z, IntOff B (s Z).lo) → (∀ Z, τ ≤ (s Z).degLo) → GoodW U (xiR D) V dict G → GoodW U (xiR D) V dict (G + G₀) ∧ rankW U (G + G₀) = rankW U G ∧ degW U (xiR D) V dict G + (rankW U G : ℝ) * (τ - logSum B) ≤ degW U (xiR D) V dict (G + G₀) := by
  intro D H Dw l Xo c r U V dict hC G₀ G s B τ hev hB hint hτ hG
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hA : ∀ G' : WTZ D.host.E, Adds U V dict G' := fun G' =>
    GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G' (GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict hU G')
      ((GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hC G').1)
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := (hA G).1.1 hG
  have hgr : ∀ Z, GoodOn U (xiR D) V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := fun Z =>
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G hU hev (hOn Z)
  have hG' : GoodW U (xiR D) V dict (G + G₀) := (hA (G + G₀)).1.2 (fun Z => (hgr Z).1)
  obtain ⟨-, hr1, -, -, hd1⟩ := (hA G).2 hG
  obtain ⟨-, hr2, -, -, hd2⟩ := (hA (G + G₀)).2 hG'
  have hrank : rankW U (G + G₀) = rankW U G := by
    rw [hr1, hr2]; exact finsum_congr fun Z => (hgr Z).2
  refine ⟨hG', hrank, ?_⟩
  haveI : Finite (Comp Xo c) := finite_comp
  letI := Fintype.ofFinite (Comp Xo c)
  have hZ : ∀ Z, degOn U (xiR D) V dict Z G + (rankOn U Z G : ℝ) * (τ - logSum B) ≤
      degOn U (xiR D) V dict Z (G + G₀) := fun Z => by
    have h1 := GlobalTheory.T.cuspForm_supLattice_degree_twist_lower_bound D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G B hU hev hB (hint Z) (hOn Z)
    have h2 : (rankOn U Z G : ℝ) * (τ - logSum B) ≤ (rankOn U Z G : ℝ) * ((s Z).degLo - logSum B) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ Z]) (Nat.cast_nonneg _)
    linarith
  rw [hd1, hd2, hr1]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro Z _
  rw [(hgr Z).2]
  linarith [hZ Z]

end GlobalTheory.Proof.TwistedWeightDegree
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

noncomputable section

namespace GlobalTheory.FlatRootTwist

theorem intOff_nsmul {K : Type} [Field K] [NumberField K] {B : Finset ℕ} {ρ : HeightOneSpectrum (𝓞 K) → ℝ}
    (h : IntOff B ρ) (n : ℕ) : IntOff B (n • ρ) := by
  intro v hv
  obtain ⟨k, hk⟩ := h v hv
  refine ⟨n * k, ?_⟩
  simp [hk]

theorem twSec_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {x : ℝ} {Z : Comp Xo c} {G G' : WTZ E} (hG : G = G') (s : TwSec U x Z G) :
    ∃ t : TwSec U x Z G', t.lo = s.lo ∧ t.degLo = s.degLo := by
  subst hG
  exact ⟨s, rfl, rfl⟩

theorem flat_root_twist : GlobalTheory.Published.AbelianDeRham → ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → FlatExists U (xiR D) → UnramPts Xo c (badPrimes H l) → ∀ (w : Psi H → ℤ) (m : ℕ), (∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) ≤ t.degLo) ∧ ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ), (∀ Z : Comp Xo c, GoodOn U (xiR D) V dict Z (wtOf Dw u n) → GoodOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankOn U Z (wtOf Dw (u + parWt Dw w) (n + m)) = rankOn U Z (wtOf Dw u n) ∧ degOn U (xiR D) V dict Z (wtOf Dw u n) + (rankOn U Z (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m))) ∧ (GoodW U (xiR D) V dict (wtOf Dw u n) → GoodW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankW U (wtOf Dw (u + parWt Dw w) (n + m)) = rankW U (wtOf Dw u n) ∧ degW U (xiR D) V dict (wtOf Dw u n) + (rankW U (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m))) := by
  intro _ D H Dw l Xo c r U V dict hC hF hpq hg hflat hB w m
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D :=
    fun σ hσ => (hC.2 σ hσ).2.2.2
  obtain ⟨hK, hroot⟩ :=
    GlobalTheory.KeyRootTw.exists_twSec_keyRoot _ H Dw l Xo c r U (xiR D) hU hξ hF hpq hg hB

  set b : ℝ := (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) -
    (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) *
      (Real.log (2 * Real.pi) / 2 + lrd D.host.E) with hb

  have hW : wtOf Dw (parWt Dw w) 0 + m • wtOf Dw 0 1 = wtOf Dw (parWt Dw w) m := by
    rw [GlobalTheory.CompHt.nsmul_wtOf, ← wtOf_add]
    simp
  have hsec : ∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m),
      IntOff (badPrimes H l) t.lo ∧ b ≤ t.degLo := by
    intro Z
    obtain ⟨t₁, h₁I, -, h₁d⟩ :=
      (GlobalTheory.FlatTwisting.twSec_of_flat _ H Dw l Xo c r U (xiR D) (badPrimes H l) hK hU hpq hB).2 hflat Z w
        (GlobalTheory.FlatLine.hasPts U hpq hg hU Z)
    obtain ⟨t₂, h₂I, h₂d⟩ := hroot Z
    have hmp := GlobalTheory.FlatTw.twSec_mul_pow _ H Dw l Xo c r U (xiR D) Z
    obtain ⟨t₃, h₃lo, h₃d⟩ := hmp.2 _ t₂ m
    obtain ⟨t₄, -, -, h₄lo, h₄d⟩ := hmp.1 _ _ t₁ t₃
    obtain ⟨t, htlo, htd⟩ := twSec_congr hW t₄
    refine ⟨t, ?_, ?_⟩
    · rw [htlo, h₄lo, h₃lo]
      exact h₁I.add (intOff_nsmul h₂I m)
    · rw [htd, h₄d, h₃d]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left h₂d hm
      rw [hb]
      nlinarith
  choose s hsI hsd using hsec
  have hBp : ∀ p ∈ badPrimes H l, p.Prime := fun p hp => badPrimes_prime p hp
  have hadd : ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ),
      wtOf Dw u n + wtOf Dw (parWt Dw w) m = wtOf Dw (u + parWt Dw w) (n + m) :=
    fun u n => (wtOf_add u (parWt Dw w) n m).symm
  refine ⟨fun Z => ⟨s Z, hsI Z, hsd Z⟩, fun u n => ⟨fun Z hZ => ?_, fun hW' => ?_⟩⟩
  · obtain ⟨hgood, hrank⟩ := GlobalTheory.FlatTw.Good.twist_goodOn _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) hU (even_wtOf u n) hZ
    have hdeg := GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) (badPrimes H l) hU (even_wtOf u n) hBp (hsI Z) hZ
    rw [hadd] at hgood hrank hdeg
    refine ⟨hgood, hrank, ?_⟩
    have hr : (0 : ℝ) ≤ (rankOn U Z (wtOf Dw u n) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right (hsd Z) (logSum (badPrimes H l))) hr
    linarith
  · obtain ⟨hgood, hrank, hdeg⟩ := GlobalTheory.Proof.TwistedWeightDegree.degW_twist D H Dw l Xo c r U V dict hC _ (wtOf Dw u n) s
      (badPrimes H l) b (even_wtOf u n) hBp hsI hsd hW'
    rw [hadd] at hgood hrank hdeg
    exact ⟨hgood, hrank, hdeg⟩

end GlobalTheory.FlatRootTwist
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection : GlobalTheory.Published.AbelianDeRham → ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → FlatExists U (xiR D) → UnramPts Xo c (badPrimes H l) → ∀ (w : Psi H → ℤ) (m : ℕ), (∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) ≤ t.degLo) ∧ ∀ (u : Weight Dw) (n : ℤ), (∀ Z : Comp Xo c, GoodOn U (xiR D) V dict Z (wtOf Dw u n) → GoodOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankOn U Z (wtOf Dw (u + parWt Dw w) (n + m)) = rankOn U Z (wtOf Dw u n) ∧ degOn U (xiR D) V dict Z (wtOf Dw u n) + (rankOn U Z (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m))) ∧ (GoodW U (xiR D) V dict (wtOf Dw u n) → GoodW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankW U (wtOf Dw (u + parWt Dw w) (n + m)) = rankW U (wtOf Dw u n) ∧ degW U (xiR D) V dict (wtOf Dw u n) + (rankW U (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m))) := by
  atlas_forward_decl GlobalTheory.FlatRootTwist.flat_root_twist
end
