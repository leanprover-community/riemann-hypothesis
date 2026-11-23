module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SphUntw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingProdIrrSupport
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MongeAmpereChartDensityIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportCharacters
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.GdLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W
section WD
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem comm_one {G H : Type} [Group G] [CommGroup H] (f : G →* H) (s t : G) : f ⁅s, t⁆ = 1 := by
  rw [map_commutatorElement]
  exact (Commute.all _ _).commutator_eq
private theorem lpDim_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (x.lpTwist ξ hξ).lpDim = x.lpDim := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.lpDim_mk, WD.lpDim_mk]
private theorem gd_lpTwist {x : WD h} (hx : Gd x) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : Gd (x.lpTwist ξ hξ) := by
  refine ⟨fun s t => ?_, (GlobalTheory.GalCut7.IwahoriTwist.monodromy_vanishes_weilTwist_iff x ξ hξ).2 hx.2⟩
  have h1 : WD.charPol x ⁅s, t⁆ = _ := hx.1 s t
  show WD.charPol _ _ = _
  rw [GlobalTheory.GalCut.SsTwist.charPol_lpTwist, comm_one ξ s t, lpDim_lpTwist, h1]
  simp
end WD
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem good_chars {n : ℕ} {x : IrrGL (k := k)} (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hs : HasSupport x.rep (GlobalTheory.RoadU.chars ξ hξ)) : Good x := by
  refine ⟨_, hs, fun y hy => Or.inl ?_⟩
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
  simp [IrrGL.ofChar]
private theorem good_zero (τ : SmIrr (GL (Fin 0) k)) : Good (IrrGL.of τ.ρ τ.smooth τ.irred) := by
  obtain ⟨t, x, hx, -, hc, -, hs⟩ := GlobalTheory.BCen.SuppEmbed.exists_embedding_prodIrr_support k 0 _ τ.ρ τ.smooth τ.irred
  refine ⟨_, ((hs _).2 rfl).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred), fun y hy => ?_⟩
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  have h0 := (Finset.sum_eq_zero_iff.1 hx) a (Finset.mem_univ a)
  have h1 := (hc a).1
  omega
end Loc
theorem sphUntw_alt : _root_.UpperTheory.V.Z.Desc.W.SphUntwAlt := by
  intro _ K Ω _ _ _ _ _ n κ w τ τ' B hB ⟨e⟩
  have hχ : IsSmoothChar (κ.loc w) := GlobalTheory.HeckeComp.smooth_loc κ w
  have ex : (IrrGL.of τ.ρ τ.smooth τ.irred).tw (κ.loc w) hχ = IrrGL.of τ'.ρ τ'.smooth τ'.irred := by
    rw [IrrGL.tw_of]
    exact IrrGL.of_eq_of.2 ⟨e.symm⟩
  have ex' : IrrGL.of τ.ρ τ.smooth τ.irred = (IrrGL.of τ'.ρ τ'.smooth τ'.irred).tw (κ.loc w)⁻¹ hχ.inv := by
    rw [← ex, IrrGL.tw_tw]
    simp only [mul_inv_cancel, IrrGL.tw_one]
  have hGG : Good (IrrGL.of τ'.ρ τ'.smooth τ'.irred) ∧ Good (IrrGL.of τ.ρ τ.smooth τ.irred) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨good_zero τ', good_zero τ⟩
    · obtain ⟨ξ, hξ, -, hs, -⟩ := GlobalTheory.T.supercuspidal_support_characters K n hn w τ' B hB
      have h1 := GlobalTheory.RoadU.CharTwist.hasSupport_rep_tw hs _ hχ.inv
      rw [GlobalTheory.RoadU.CharTwist.chars_tw, ← ex'] at h1
      exact ⟨good_chars ξ hξ hs, good_chars _ _ h1⟩
  obtain ⟨hG', hG⟩ := hGG
  refine ⟨hG, fun A h rc hrc => ?_⟩
  obtain ⟨b, hb, ε, L⟩ := toV' hrc
  have hsph := GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL hB
  have hu : (rc (IrrGL.of τ'.ρ τ'.smooth τ'.irred)).unr :=
    (L.sph _).1 (fixed_ne_bot_of_equiv (IrrGL.equivOf τ'.ρ τ'.smooth τ'.irred) hsph)
  have hg := (UpperTheory.V.Z.Win.Gu.gdLaws K Ω A w h).2.2.2 _ hu
  rw [algNorm, L.nu_eq, (UpperTheory.V.Z.Win.Gu.gdLaws K Ω A w h).2.1, ex', L.twist _ _ _ hG', L.one, lpChar_lpOfChar]
  exact gd_lpTwist hg _ _
end UpperTheory.V.Z.Desc.W
end
end
