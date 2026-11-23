module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_level_algClosed_charZero :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (P : PolAV (Sp C)) (k : ℕ), 1 ≤ k → ∃ ζ : Cˣ, Nonempty (Out.Level P k (unitOn ζ)) := by
  intro C _ _ _ P k hk
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : NeZero (k : C) := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C k
  let ze : Cˣ := (hζ.isUnit (by omega)).unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 (by simpa [ze] using hζ)
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk0 ze hze
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : C →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k := fun φ =>
    hze.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp C) P k (unitOn ze)
    (by have := nt C; exact prim (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 (by omega))
    pt hpt hw
  exact ⟨ze, ⟨lev⟩⟩

end GlobalTheory.MBLow
