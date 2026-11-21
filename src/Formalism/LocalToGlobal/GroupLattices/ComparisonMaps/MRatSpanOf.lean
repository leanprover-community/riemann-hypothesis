import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanRec

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatX (ξ : G.P.Xsp) : Prop := ∃ Q : MvPolynomial _ LL, MvPolynomial.map e Q = ξ

def RatActG : Prop := ∀ (i : G.comp) (γ : (G.lev i).Γ) (ξ : G.P.Xsp), RatX G e ξ →
  RatX G e (((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ)

def HRat : Prop := ∀ L : G.P.Tup, G.P.IsLatTup L →
  G.P.HtupW L ≤ Submodule.span G.O {ξ | ξ ∈ G.P.HtupW L ∧ RatX G e ξ}



end Formalism.L2.G.Cmp
