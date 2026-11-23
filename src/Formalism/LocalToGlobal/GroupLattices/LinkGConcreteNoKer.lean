module

public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleFamilyNoKernel
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescFOfValRatF
public import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdSubF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i) := by
  obtain ⟨x0, h0⟩ := h.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨ht, hx1⟩ := h0 x hx i
  obtain ⟨G⟩ := ht hx1
  exact stdSubAt_of_ring _ G.ring

theorem gatEF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i) := by
  obtain ⟨x0, h0⟩ := h.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨ht, hx1⟩ := h0 x hx i
  obtain ⟨G⟩ := ht hx1
  exact gatE_of_gatIs _ G.herm.lev0
    (fun u => Triv.trivStabU (G.herm.lev0 u) (Fm.D x i).host.g_prime (Fm.D x i).host.g_ne) G.gat

theorem npDescF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : NPDescF Fm := by
  refine Cmp.npDescF_of_valRatF Fm ?_
  obtain ⟨x0, h0⟩ := h
  exact ⟨x0, fun x hx i hx1 => by
    obtain ⟨G⟩ := h0 x hx i hx1
    exact Cmp.CmpTied.valRat G.cmp⟩

theorem linkG_concrete_noKer (𝒞 : FamClass) (h : Loc)
    (hT : Closed 𝒞 fun Fm _ => GroupCompatibilityFamily Fm) (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  link_of_local_closed 𝒞 h (hT.imp fun Fm _ _ ht => gatEF_of_tied Fm ht) (hT.imp fun Fm _ _ ht => stdSubF_of_tied Fm ht)
    h2 (hT.imp fun Fm _ _ ht => npDescF_of_tied Fm ht)

theorem linkG_concrete5 (𝒞 : FamClass) (hT : Closed 𝒞 fun Fm _ => GroupCompatibilityFamily Fm) (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  linkG_concrete_noKer 𝒞 loc_proved hT h2

end Formalism.L2.G
