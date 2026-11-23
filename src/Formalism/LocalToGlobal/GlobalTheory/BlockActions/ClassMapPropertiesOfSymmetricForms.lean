module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfFinite
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.AdelicLocalLattice
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.DualLStable
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.PrVTensInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def DualLoc (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls D.R.m) (z : Fin (D.R.N D.R.m) → D.host.E), z ∈ Ld D u D.R.m le_rfl c →
    ((bc (prV (E := D.host.E) (Tf.atT.eV v).1) ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (z a)) ∈
      latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
          (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb))

def FvStab (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
      (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
      (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)

theorem stabLF_of_fv (Tf : FormsTiedSym D u Ch chOf) (hF : FvStab Tf) : StabLF Tf :=
  stabLF_of Tf (fun c γ hγ => ⟨stab_lat Tf latLocGlob adelic_local_lattice c γ hγ, hF c γ hγ⟩)

theorem stabiliser_bijective_self_dual
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      FvStab Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_finite hSD (fun D u Ch chOf Tf => stabLF_of_fv Tf (hF D u Ch chOf Tf))

end Formalism.L2.GlobalTheoryTheory.Br
