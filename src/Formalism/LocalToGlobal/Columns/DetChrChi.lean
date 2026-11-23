module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
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
public import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hspan : Submodule.span E (stdLat E n : Set (Sp E n)) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    simpa using (single_mem_stdLat (E := E) (n := n) i 1)
  have hlat := Formalism.UG.P.csGlob_lattice (F := F) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) hspan x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.toIsLattice.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rel

end DetChrChi

end Formalism.L2.Col
