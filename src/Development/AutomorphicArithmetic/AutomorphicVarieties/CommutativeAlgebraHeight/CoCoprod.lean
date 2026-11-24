module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Coprod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem co_coprod_pres (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] :
    ∃ W : WPres O Unit R, ∀ s, W.z s ∈ maximalIdeal R := by
  obtain ⟨n, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (maximalIdeal R))
  have hm : ∀ s, z s ∈ maximalIdeal R := fun s => hz ▸ Submodule.subset_span ⟨s, rfl⟩
  haveI : IsCO O (MvPowerSeries (Fin n) O) := co_mvps O O (Fin n)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R (Fin n) (Algebra.ofId _ _) z hm
  refine ⟨⟨Fin n, fun _ => (), F, ?_, ?_⟩, fun s => ?_⟩
  · refine co_surj O _ R _ (le_trans ?_ le_sup_left)
    rw [← hz, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [← hF s]
    refine Ideal.mem_map_of_mem _ fun hu => ?_
    simpa using MvPowerSeries.isUnit_constantCoeff _ hu
  · intro g hg j
    have : wcomp O (fun _ : Fin n => ()) j g = g := by
      ext a
      rw [coeff_wcomp, if_pos (Subsingleton.elim _ _)]
    rwa [this]
  · show F (MvPowerSeries.X s) ∈ _
    rw [hF]
    exact hm s

theorem UpperTheory.V.CA.co_coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (T : Type) [Finite T] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra O (B t)] [∀ t, IsCO O (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : ∀ t, B t →ₐ[O] R), ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ t, B t →ₐ[O] R'), ∃! g : R →ₐ[O] R', ∀ t, g.comp (j t) = f t := by
  intro O _ _ _ _ T _ B _ _ _
  haveI := Fintype.ofFinite T
  choose WB hWB using fun t => co_coprod_pres O (B t)
  obtain ⟨R, i1, i2, i3, i, _, _, h, -⟩ := UpperTheory.V.Alg.coprod O Unit T B WB hWB
  exact ⟨R, i1, i2, i3, i, h⟩
