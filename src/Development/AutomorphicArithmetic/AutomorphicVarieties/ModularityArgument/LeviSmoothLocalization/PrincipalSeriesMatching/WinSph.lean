module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnlFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUnl
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.Z.Gam
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter


variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = unrChar k a := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
  have h0 : x ≠ 0 := fun e => ValuativeRel.uniformizer_ne_zero (R := k) (by rw [← hx, e, map_zero])
  exact ⟨_, eq_unrChar h (ϖ := Units.mk0 x h0) hx⟩

private theorem exists_family {n : ℕ} {s : Multiset (IrrGL (k := k))} (h1 : ∀ y ∈ s, y.1 = 1) (hn : (s.map Sigma.fst).sum = n)
    (hu : ∀ ξ ∈ chars s, IsUnram ξ) : ∃ α : Fin n → ℂˣ,
      s = Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) := by
  have hc : Multiset.card s = n := by
    rw [← hn, Multiset.map_congr rfl h1, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  obtain ⟨x, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_fin_enum s hc
  have key : ∀ i, ∃ a : ℂˣ, x i = IrrGL.ofChar (unrChar k a) (isSmoothChar_of_isUnram (isUnram_unrChar k a)) := fun i => by
    have hm : x i ∈ Finset.univ.val.map x := Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    obtain ⟨θ, hθ, e⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar (x i) (h1 _ hm)
    obtain ⟨a, rfl⟩ := exists_unr (hu θ ⟨hθ, e ▸ hm⟩)
    exact ⟨a, e⟩
  choose α hα using key
  exact ⟨α, congrArg (fun f => Multiset.map f Finset.univ.val) (funext hα)⟩


theorem winSph : WinSph := by
  intro K _ _ _ n hn π t v hw hu
  obtain ⟨⟨s, hs⟩, -, h3, -⟩ := suppFacts K n hn π v
  obtain ⟨h4, h5, -⟩ := h3 s hs
  have hl := winUnl K n π t v hw s hs
  obtain ⟨α, rfl⟩ := exists_family (h4.1 hw.1) h5 (hu s hs)
  obtain ⟨σ, hσ, hs⟩ := hs
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  have hq : GroundTheory.LocalField.residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  obtain ⟨e⟩ := unlFull (v.adicCompletion K) n σ.V σ.ρ _ _ hs (hq ▸ hl)
  exact ⟨_, (CG.hasSat_mk π v _).2 (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ
    (GlobalTheory.PrinSat.hasSatGL_of_equiv e (GlobalTheory.PrinSat.hasSatGL_prinSeries v α)))⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
