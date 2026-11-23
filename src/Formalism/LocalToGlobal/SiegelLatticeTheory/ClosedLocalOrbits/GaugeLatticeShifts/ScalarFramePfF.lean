module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfB
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Concrete

variable {D : D7} (Z : LocDat D) (p : PlF D)

def IotaEl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ g : Loc.SplitG (Z.M p).L, (Z.M p).split = some g →
    IotaG (locH Z p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ)
      (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g1 b))
      (fun b => sF' Z p b • baseChange₂ D p (g2 b)) (betaP p β)

theorem omp_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Z.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Z.hcj p), cj_iota (Z.hcj p)]
  congr 2 <;> ring

end Concrete

end Formalism.L2.SG.Pf.ScalarFramePf
