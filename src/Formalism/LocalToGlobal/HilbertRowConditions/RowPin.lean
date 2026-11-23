module

public import Formalism.LocalToGlobal.ClassSK
public import Formalism.LocalToGlobal.HermitianForms.TiedBr
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def LowerMapTieS {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Formalism.L2.Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u D.R.m)) (Formalism.L2.Forms.mZ u Tf.til.z0) P
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen D u P)

def LowerMapTieTw {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} (T : TiedDataSK ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m) : Prop :=
  IsUnit (Formalism.L2.Forms.bZ u (T.tw.pt.til u μ hμ h1).z0).det → ∀ (ψ : (D.PTw u μ).Wz) (c : (ex.tw.fm u μ).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, T.tw.ptE.eWz u μ ψ c s =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u D.R.m)) (Formalism.L2.Forms.mZ u (T.tw.pt.til u μ hμ h1).z0) P
        (Formalism.L2.Forms.twYS T.tw.ch T.cols.forms u μ D.R.m le_rfl s)) →
    (T.tw.pt.val u μ hμ).eW ((D.PTw u μ).lowerMap ψ) c =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen D u P)


end Formalism.L2.Rows

end
