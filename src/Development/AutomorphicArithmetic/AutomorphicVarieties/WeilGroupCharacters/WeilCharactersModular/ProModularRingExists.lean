module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UniversalDeformationRingNonemptyOfNonemptyPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

theorem UpperTheory.V.W.b0Ex :
    PhiAll → ProModularRingExists := by
  intro h l hl L Ω _ _ _ _ _ _ s V c n r R _ _ _ hp
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨-, h0, hv⟩ := h l L Ω s V
  exact UpperTheory.V.CA.universalDeformationRing_nonempty_of_nonempty_pair r h0 hv ⟨R, _, _, inferInstance, hp⟩
