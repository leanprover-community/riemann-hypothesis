module

public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
open CategoryTheory Limits

namespace LateralTheory.E.SepTensorPf

theorem SepTensor_of : LateralTheory.E.SHTensorPf.SepTensor := by
  intro A X B Z x b u v hp _ hX _ hb _ hZ
  obtain ⟨_, hXs⟩ := hX
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  let f : X →+* IsLocalRing.ResidueField Z := (IsLocalRing.residue Z).comp u.hom
  have hf : f.IsIntegral := RingHom.IsIntegral.trans u.hom (IsLocalRing.residue Z) hu
    (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective)
  let _ : Algebra X (IsLocalRing.ResidueField Z) := f.toAlgebra
  have : Algebra.IsIntegral X (IsLocalRing.ResidueField Z) := ⟨hf⟩
  have : Algebra.IsIntegral (IsLocalRing.ResidueField X) (IsLocalRing.ResidueField Z) :=
    Algebra.IsIntegral.tower_top X
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField X)

end LateralTheory.E.SepTensorPf
