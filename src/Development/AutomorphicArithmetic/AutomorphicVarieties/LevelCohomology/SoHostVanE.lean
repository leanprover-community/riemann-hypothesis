module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineNeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoVanEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.hostVanE : ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → UnitaryThreeInertia.HostVanE := by
  intro CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF
  apply So.vanEOf c.O _ _ _ F
  intro j hj s
  rcases hj.lt_or_eq with hlt | heq
  · exact So.lineNeg CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω l c N e ψ S A F hD.e_pos hF j hlt s
  · subst heq
    exact So.lineZero c.O _ _ _ F (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hD S A F hF) s
