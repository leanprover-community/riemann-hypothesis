module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_root (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} (hm : 0 < m)
    (d : Ideles E) (hd : pFin E (d : Ad E) = 1) : ∃ y : Ideles E, y ^ m = d := by
  have h : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = (d : Ad E).1 w := fun w => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ((d : Ad E).1 w)) hm
    exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  choose y hy using h
  let Y : Ad E := ((y : InfiniteAdeleRing E), (1 : Af E))
  have hY : Y ^ m = (d : Ad E) := Prod.ext (funext hy) ((one_pow m).trans hd.symm)
  have hu : IsUnit Y := (isUnit_pow_iff hm.ne').1 (hY ▸ d.isUnit)
  exact ⟨hu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, hu.unit_spec, hY])⟩

theorem UpperTheory.detCharacter_ker_open_trivial_rational_archimedean :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E) (m : ℕ), 0 < m → ν.OrderDvd m → IsOpen (((chiDet n ν).comp (UA E n).subtype).ker : Set (UA E n)) ∧ (∀ g ∈ ratU E n, chiDet n ν (g : UA E n) = 1) ∧ ∀ g ∈ infU E n, chiDet n ν (g : UA E n) = 1 := by
  intro E _ _ _ n ν m hm h
  have h1 : ∀ x, ν.1 x ^ m = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) h
  refine ⟨isOpen_ker_of_pow _ ?_ hm fun g => h1 _, ?_, ?_⟩
  · exact ν.2.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  · intro g hg
    obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 hg
    rw [← hγ, chiDet_ratGL]
  · intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (pFin E) (g : GA E n) = 1 := hg
    obtain ⟨y, hy⟩ := exists_root E hm (Matrix.GeneralLinearGroup.det (g : GA E n)) (by
      rw [← GlobalTheory.CuspRep.det_map, hg']; simp)
    change ν.1 (Matrix.GeneralLinearGroup.det (g : GA E n)) = 1
    rw [← hy, map_pow, h1]
