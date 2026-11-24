module

public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ClsPLocBasis

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem exists_isLocBasis_clsP : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (w : D.what₂.places.Pl) (c : (D.fm u).clsP),
    ∃ B : GL (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) B := by
  intro D u Ch chOf Tf w c
  have hL : Submodule.IsFullLattice D.host.E (Tf.clsP.lat c) :=
    Formalism.MainNotions.G.ChF.isLattice_of_hat Tf.clsP.lev.Lb (Tf.clsP.lat c) Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span
      (Tf.clsP.y c).1 (Tf.clsP.y_lat c)
  have hspan : Submodule.span D.host.E (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) = ⊤ := by
    have hG := Formalism.UG.P.csGlob_lattice (F := D.host.F) Tf.clsP.lev.Lb Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span (Tf.clsP.y c).1
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact Formalism.L2.GlobalTheoryTheory.Br.latS_mem_span (F := D.host.F) _ x ((Tf.clsP.y_lat c _).2 hx)
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (D.what₂.places.resChar w) D.host.E (Tf.clsP.lat c) hL.fg hspan

end GlobalTheory.ClsPLocBasis
