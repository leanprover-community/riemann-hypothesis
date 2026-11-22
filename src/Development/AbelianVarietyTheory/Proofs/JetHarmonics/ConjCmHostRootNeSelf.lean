module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeafCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj (Q : Par D) (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h2 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h2
  exact conj_cmHostRoot_ne_self Q.H h2

theorem wtA_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj Q hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj Q hp, this]
  · simp

end GlobalTheory.LeafCompare
