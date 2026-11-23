module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatKOfStdL
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerSiteSelfDual

theorem isSDLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {n N : ℕ} (h : n = N)
    {L : Submodule (𝓞 E) (Fin n → E)} {M : Submodule (𝓞 E) (Fin N → E)} (hL : HEq L M) (hM : Formalism.BasicNotions.IsSDLat E N M) :
    Formalism.BasicNotions.IsSDLat E n L := by
  subst h
  cases hL
  exact hM



theorem even_and_isSDLat_kerN : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j ≤ D.R.m → ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → Even (((sysS H X std).Pj j).m + 1) ∧ IsSDLat D.host.E (((sysS H X std).Pj j).m + 1) ((J.fd std).kerN j La) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hk, -⟩ := hD j hj La hLa
  refine ⟨hr ▸ Formalism.MainNotions.product_zeroth_first_parts.N_even D.R j, isSDLat_of_heq hr hk ?_⟩
  exact GlobalTheory.KerSelfDual.isSDLat_latK_of_stdL ((J.St j hj).K (J.chart std j hj La)).lev (J.A.crd j hj) J.a
    (J.pins.crd_orth j hj) (J.base j hj _) (J.pt std j hj La)

end GlobalTheory.KerSiteSelfDual
