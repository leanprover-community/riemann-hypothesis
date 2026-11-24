module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.phiCond :
    LocalPublishedTheorems → ∀ (v l : ℕ) [Fact v.Prime] [Fact l.Prime] (H : Subgroup (GQ v)), IsOpen (H : Set (GQ v)) → Finite {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)} := by
  intro hP v l _ _ H hH
  letI : Algebra ℤ_[l] (ZMod l) := (PadicInt.toZMod (p := l)).toAlgebra
  letI : TopologicalSpace (ZMod l) := ⊥
  haveI : DiscreteTopology (ZMod l) := ⟨rfl⟩
  let ρ : Representation (ZMod l) H (ZMod l) := 1
  have hρ : ContAction ρ := continuous_snd
  have hfin := (tateFin hP (v := v) (l := l) H.subtype hH.isOpenEmbedding_subtypeVal (ZMod l) (ZMod l) ρ hρ).1
  haveI : Finite (H1 ρ) := Module.finite_of_finite (ZMod l)
  have hc : ∀ f : {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)},
      (fun g => Multiplicative.toAdd (f.1 g)) ∈ Z1 ρ := by
    intro f
    refine ⟨?_, fun g h => ?_⟩
    · refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
      refine ⟨(fun x => g⁻¹ * x) ⁻¹' (f.1.ker : Set H), f.2.preimage (by fun_prop), by simp, fun x hx => ?_⟩
      have : f.1 (g⁻¹ * x) = 1 := hx
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      rw [this]
    · simp [ρ]
  refine Finite.of_injective (fun f => (Submodule.Quotient.mk ⟨_, hc f⟩ : H1 ρ)) fun f f' hff => ?_
  have h1 := (Submodule.Quotient.eq ((ReciprocityTheory.Gal.B1 ρ).comap (Z1 ρ).subtype)).1 hff
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 (Submodule.mem_comap.1 h1)
  refine Subtype.ext (MonoidHom.ext fun g => Multiplicative.toAdd.injective ?_)
  have := hm g
  simpa [ρ, sub_eq_zero] using this
