module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.LogLeExp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TupExact
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix UpperTheory.V

namespace UpperTheory.V.KT

theorem sx_exact (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.FaceExactTo (Sx L N) (Sx.face L N) m := by
  obtain ⟨h1, h2, h3⟩ := ConeExtensionAcyclic.acyc_simp (good L N)
  exact KH.tupExact _ _ h1 (by rw [h2]; exact Set.univ_nonempty) h3 m

theorem orbBound_mono (L : Type) [Field L] [NumberField L] (N : ℕ) {p p' : ℕ} (h : p ≤ p') :
    orbBound L N p ≤ orbBound L N p' := by
  unfold orbBound
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ?_)
  exact Nat.mul_le_mul_left _ (by omega)

theorem tors_le (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.TorsLe (K.HGL L N m) (KH.bound m (orbBound L N m) (3 ^ (dd L N * N)) (m + 2)) :=
  KH.mainFace (Gm L N) (Sx L N) (Sx.face L N) Sx.face_smul m _ _ (Nat.one_le_pow _ _ (by norm_num))
    (sx_exact L N m)
    (fun p hp => ⟨(orb L N p).1, (orb L N p).2.trans (orbBound_mono L N hp)⟩)
    (fun p _ => stab L N p)

end UpperTheory.V.KT
