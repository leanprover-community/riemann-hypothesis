module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfF
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ScalarFrameCT : Prop :=
  ∀ (D : D7) (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Tn T'n : ℕ),
    FixedHyp D Λ F → IsLift Λ F' → IsLift Λ F'' → IsFixedConv Λ (gS D) F' → IsFixedConv Λ (gS D) F'' →
    IsAdmissible Λ (gS D) F F' → IsAdmissible Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    Lat.s0 Λ F F' F'' β D.R.k = 1 → IsScalar Λ F F' F'' β → Gval F F' ≠ 0 → Gval F F'' ≠ 0 →
    T ≠ 0 → T' ≠ 0 →
    ∀ p : PlF D, (locH Z p).IsScalarPair (locTerm Z p Λ F F' Tn T'n) (locTerm Z p Λ F F'' Tn T'n)

def IotaStep : Prop :=
  ∀ (D : D7) (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    FixedHyp D Λ F → IsLift Λ F' → IsLift Λ F'' → IsFixedConv Λ (gS D) F' → IsFixedConv Λ (gS D) F'' →
    IsAdmissible Λ (gS D) F F' → IsAdmissible Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    Lat.s0 Λ F F' F'' β D.R.k = 1 → IsScalar Λ F F' F'' β → Gval F F' ≠ 0 → Gval F F'' ≠ 0 →
    T ≠ 0 → T' ≠ 0 →
    ∀ p : PlF D, IotaEl Z p Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹)
      (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

end Formalism.L2.SG.Pf
