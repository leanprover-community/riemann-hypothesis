module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
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

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtTorus

theorem isTorus_splitTorus (k : Type u) [Field k] (X : Type u) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] : IsTorus (splitTorus (Spec (CommRingCat.of k)) X) :=
  ⟨GlobalTheory.Diag.isCommMonObj _ X, inferInstance, inferInstance,
    ⟨k, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
      GlobalTheory.Diag.baseChangeIso _ X, GlobalTheory.Diag.baseChangeIso_isMonHom _ X⟩⟩

def torusExtOfSplit {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
    (E : TorusExtension G) : TorusExt G :=
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  { B := E.B
    isAbelian := E.isAbelian
    q := E.q
    q_hom := E.q_hom
    q_flat := E.q_flat
    q_surjective := E.q_surjective
    q_quasiCompact := E.q_quasiCompact
    T₀ := splitTorus (Spec (CommRingCat.of k)) E.X
    isTorus := isTorus_splitTorus k E.X
    i := E.i
    i_hom := E.i_hom
    isKernel := E.isKernel }

theorem nonempty_torusExt_of_split : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExtension G) → Nonempty (TorusExt G) :=
  fun _ _ _ _ h => h.map torusExtOfSplit

end GlobalTheory.SplitExtTorus
