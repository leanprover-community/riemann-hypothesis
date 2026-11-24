module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRowsStatement
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
namespace GlobalTheory
theorem V0_map_iota_eq_top_of_real_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s → P.A3.fam3.TypesSep3 → PrimRows3 Q.Rl Q.F → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q s hOk hSep hPrim
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  exact GlobalTheory.T.rowMap_surjective_of_primitiveRows D P.Gp P.Pl0 P.I0 P.T P.A3 Ks Q.Rl P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.Dc P.Sp P.C P.NuC P.I
    Dcf Spf Zscf s P.tied.div hOk hSep Q.charW hPrim Q.zs Q.s1
end GlobalTheory
end
