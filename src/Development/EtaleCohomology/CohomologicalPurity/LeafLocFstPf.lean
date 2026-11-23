module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ disc))

theorem LeafLocFst_of (hZ : LeafZ) : LeafLocFst := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hE H d P V q hq i
  have := P.cl
  obtain ⟨⟨z, hpb⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) (eta H P V)
  have hpb' := hpb.map sch
  have := H.hens Γ(P.X, V.1) (P.ι.ker.ideal V)
  have hu : IsUnit (q : H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) := by
    simpa using hq.map ((eta H P V).comp (P.X.presheaf.map (homOfLE le_top).op).hom)
  have e : pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι) = hpb'.isoPullback.inv ≫
      sch.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((P.ι.ker.ideal V).map (eta H P V))))) :=
    hpb'.isoPullback_inv_fst.symm
  rw [e]
  exact eqv_comp (eqv_iso _ _) (hE q _ _ hu i)

end LateralTheory.CohomologicalPurity.TubeCut
