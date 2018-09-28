package learning.ski_calculus

object SKI {

  trait λ {
    type eval<:λ
    type ap[_<:λ]<:λ
  }

  def Eq[A<:λ, B<:λ](implicit ev: A#eval =:= B#eval) = true

  trait λFinn extends λ {
     type ap[n<:λ] = eval#ap[n]
  }

  trait ~[x<:λ,y<:λ] extends λ {
    type self = x#ap[y]
    type ap[z<:λ] = self#ap[z]
    type eval = self#eval
  }

  trait Ap2 extends λ { type ap2[x<:λ,y<:λ] = ap[x]#ap[y] }
  trait Ap3 extends Ap2 { type ap3[x<:λ,y<:λ,z<:λ] = ap[x]#ap[y]#ap[z] }
  trait Ap4 extends Ap3 { type ap4[x<:λ,y<:λ,z<:λ,w<:λ] = ap[x]#ap[y]#ap[z]#ap[w] }

  trait λF1 { type ap[x<:λ]<:λ }
  trait λ1_1[F<:λF1, x<:λ] extends λFinn { type eval = F#ap[x]#eval }
  trait λ1[F<:λF1] extends λ{
    type eval = λ1[F]
    type ap[x<:λ] = λ1_1[F,x]
  }

  trait λF2 { type ap[x<:λ, y<:λ]<:λ }
  trait λ2_2[F<:λF2, x<:λ, y<:λ] extends λFinn { type eval = F#ap[x,y]#eval }
  trait λ2_1[F<:λF2, x<:λ] extends λ{
    type eval = λ2_1[F,x]
    type ap[y<:λ] = λ2_2[F,x,y]
  }
  trait λ2[F<:λF2] extends Ap2{
    type eval = λ2[F]
    type ap[x<:λ] = λ2_1[F,x]
  }

  trait λF3 { type ap[x<:λ, y<:λ, z<:λ]<:λ }
  trait λ3_3[F<:λF3, x<:λ, y<:λ, z<:λ] extends λFinn { type eval = F#ap[x,y,z]#eval }
  trait λ3_2[F<:λF3, x<:λ, y<:λ] extends λ{
    type eval = λ3_2[F,x,y]
    type ap[z<:λ] = λ3_3[F,x,y,z]
  }
  trait λ3_1[F<:λF3, x<:λ] extends Ap2{
    type eval = λ3_1[F,x]
    type ap[y<:λ] = λ3_2[F,x,y]
  }
  trait λ3[F<:λF3] extends Ap3{
    type eval = λ3[F]
    type ap[x<:λ] = λ3_1[F,x]
  }

  trait λF4 { type ap[x<:λ, y<:λ, z<:λ, w<:λ]<:λ }
  trait λ4_4[F<:λF4, x<:λ, y<:λ, z<:λ, w<:λ] extends λFinn { type eval = F#ap[x,y,z,w]#eval }
  trait λ4_3[F<:λF4, x<:λ, y<:λ, z<:λ] extends λ{
    type eval = λ4_3[F,x,y,z]
    type ap[w<:λ] = λ4_4[F,x,y,z,w]
  }
  trait λ4_2[F<:λF4, x<:λ, y<:λ] extends Ap2{
    type eval = λ4_2[F,x,y]
    type ap[z<:λ] = λ4_3[F,x,y,z]
  }
  trait λ4_1[F<:λF4, x<:λ] extends Ap3{
    type eval = λ4_1[F,x]
    type ap[y<:λ] = λ4_2[F,x,y]
  }
  trait λ4[F<:λF4] extends Ap4{
    type eval = λ4[F]
    type ap[x<:λ] = λ4_1[F,x]
  }

  type I = λ1[λF1 { type ap[x<:λ] = x }]
  type K = λ2[λF2 { type ap[x<:λ,y<:λ] = x }]
  type S = λ3[λF3 { type ap[x<:λ,y<:λ,z<:λ] = x#ap[z]#ap[y#ap[z]] }]
  /*
  trait I_ extends λF1 { type ap[x<:λ] = x }
  trait I extends λ1[I_]

  trait K_ extends λF2 { type ap[x<:λ,y<:λ] = x }
  trait K extends λ2[K_]

  trait S_ extends λF3 { type ap[x<:λ,y<:λ,z<:λ] = x#ap[z]#ap[y#ap[z]] }
  trait S extends λ3[S_]
  */

  type I2 = S#ap2[K,K]

  trait α extends λ {type eval = α}
  trait ∅ extends λ {type eval = ∅}
  trait d1 extends λ {type eval = d1}
  trait d2 extends λ {type eval = d2}
  trait d3 extends λ {type eval = d3}
  Eq[d1, I#ap[d1]]
  Eq[d1, K#ap[d1]#ap[d2]]
  Eq[d1, S#ap[K]#ap[K]#ap[d1]]
  Eq[d1, I2#ap[d1]]


  type T = λ2[λF2 { type ap[x<:λ,y<:λ] = x }]
  type F = λ2[λF2 { type ap[x<:λ,y<:λ] = y }]

  type And = λ2[λF2 { type ap[x<:λ,y<:λ] = x#ap[y]#ap[x] }]
  Eq[T, And#ap[T]#ap[T]]
  Eq[F, And#ap[T]#ap[F]]
  Eq[F, And#ap[F]#ap[T]]
  Eq[F, And#ap[F]#ap[F]]

  type Or = λ2[λF2 { type ap[x<:λ,y<:λ] = x#ap[x]#ap[y] }]
  Eq[T, Or#ap[T]#ap[T]]
  Eq[T, Or#ap[T]#ap[F]]
  Eq[T, Or#ap[F]#ap[T]]
  Eq[F, Or#ap[F]#ap[F]]
  Eq[T, Or#ap2[T,T]]
  Eq[T, Or#ap2[T,F]]
  Eq[T, Or#ap2[F,T]]
  Eq[F, Or#ap2[F,F]]

  type If = λ3[λF3 { type ap[m<:λ,a<:λ,b<:λ] = m#ap[a]#ap[b] }]
  Eq[d1, If#ap[T]#ap[d1]#ap[d2]]
  Eq[d2, If#ap[F]#ap[d1]#ap[d2]]
  Eq[d1, If#ap3[T,d1,d2]]
  Eq[d2, If#ap3[F,d1,d2]]
  Eq[d1, If#ap[T]#ap2[d1,d2]]
  Eq[d2, If#ap[F]#ap2[d1,d2]]

  Eq[d1, If ~ T ~ d1 ~ d2]
  Eq[d2, If ~ F ~ d1 ~ d2]

  // Pairs
  type Ky = λ2[λF2 { type ap[x<:λ,y<:λ] = y }]
  type pair = λ3[λF3 { type ap[x<:λ,y<:λ,z<:λ] = z ~ x ~ y }]
  type fst = λ1[λF1 { type ap[x<:λ] = x ~ K }]
  type snd = λ1[λF1 { type ap[x<:λ] = x ~ Ky }]
  Eq[d1, fst ~ (pair ~ d1 ~ d2)]
  Eq[d2, snd ~ (pair ~ d1 ~ d2)]

  type NIL = pair ~ T ~ T
  type ISNIL = fst
  type CONS = λ2[λF2 { type ap[h<:λ,t<:λ] = pair ~ F ~ (pair ~ h ~ t) }]
  type HEAD = λ1[λF1 { type ap[z<:λ] = fst ~ (snd ~ z) }]
  type TAIL = λ1[λF1 { type ap[z<:λ] = snd ~ (snd ~ z) }]

  type L_d1 = CONS ~ d1 ~ NIL
  type L_d21 = CONS ~ d2 ~ L_d1
  // type L_d21 = CONS ~ d2 ~ (CONS ~ d1 ~ NIL)
  Eq[T, ISNIL ~ NIL]
  Eq[F, ISNIL ~ L_d1]
  Eq[d1, HEAD ~ L_d1]
  Eq[L_d1, TAIL ~ L_d21]
  Eq[NIL, TAIL ~ L_d1]
  Eq[T, ISNIL ~ (TAIL ~ L_d1)]


  type Yx[f<:λ] = λ1[λF1 { type ap[x<:λ] = f ~ (x ~ x) }] 
  type Y = λ1[λF1 { type ap[f<:λ] = Yx[f] ~ Yx[f] }]

  /*
  def contains(X, list) = list match {
    case Nil => false
    case h :: t => h == X || contains(X, t)
  }
  */

  type CONTAINS_[x<:λ] = λ2[λF2 {
    type ap[f<:λ,l<:λ] = If ~ (ISNIL ~ l) ~ F ~ cmpHT[f,HEAD ~ l,TAIL ~ l]
    type cmpHT[f<:λ,h<:λ,t<:λ] = Or ~ cmpH[h] ~ (f ~ t)
    type cmpH[h<:λ] = h
    }]
  type CONTAINS = λ2[λF2 { type ap[x<:λ,l<:λ] = (Y ~ CONTAINS_[x]) ~ l }]

  type TFF = CONS ~ T ~ (CONS ~ F ~ (CONS ~ F ~ NIL))
  type FTF = CONS ~ F ~ (CONS ~ T ~ (CONS ~ F ~ NIL))
  type FFT = CONS ~ F ~ (CONS ~ F ~ (CONS ~ T ~ NIL))
  type FFF = CONS ~ F ~ (CONS ~ F ~ (CONS ~ F ~ NIL))
  Eq[F, CONTAINS ~ T ~ FFF]
  Eq[T, CONTAINS ~ T ~ FFT]
  Eq[T, CONTAINS ~ T ~ FTF]
  Eq[T, CONTAINS ~ T ~ TFF]

  // ====================================================================================================================
  // Church numerals

  type N0 = λ2[λF2 { type ap[f<:λ,x<:λ] = x }]
  type N1 = λ2[λF2 { type ap[f<:λ,x<:λ] = f ~ x }]
  type N2 = λ2[λF2 { type ap[f<:λ,x<:λ] = f ~ (f ~ x) }]
  type N3 = λ2[λF2 { type ap[f<:λ,x<:λ] = f ~ (f ~ (f ~ x)) }]
  type SUCC = λ3[λF3 { type ap[n<:λ,f<:λ,x<:λ] = f ~ (n ~ f ~ x) }]
  type N4 = SUCC ~ N3

  //trait NFn[a<:λ,b<:λ] extends λ {type eval = NFn[a#eval,b#eval]; type ap[x<:λ] = NFn[x,NFn[a,b]] }
  //trait NF1[a<:λ     ] extends λ {type eval = NF1[a#eval       ]; type ap[x<:λ] = NFn[x,a] }
  //type NF0 = NF1[∅]
  trait NF[x<:λ] extends λ {type eval = NF[x#eval]; type ap[y<:λ] = NF[NF[y]] }
  trait NF0 extends λ {type eval = NF0; type ap[x<:λ] = NF[x] }
  type NumEval[N<:λ] = N ~ NF0 ~ α
  def NumEq[A<:λ, B<:λ](implicit ev: NumEval[A]#eval =:= NumEval[B]#eval) = true

  val n0 : NumEval[N0]#eval = null
  val n1 : NumEval[N1]#eval = null
  val n2 : NumEval[N2]#eval = null
  val n3 : NumEval[SUCC ~ N2]#eval = null

  NumEq[N1, SUCC ~ N0]
  NumEq[N2, SUCC ~ N1]
  NumEq[N2, SUCC ~ (SUCC ~ N0)]

  type xF = λ1[λF1 { type ap[_<:λ] = F }]
  type ISZERO = λ1[λF1 { type ap[n<:λ] = n ~ xF ~ T }]
  Eq[T, ISZERO ~ N0]
  Eq[F, ISZERO ~ N1]

  type PLUS = λ4[λF4 { type ap[m<:λ,n<:λ,f<:λ,x<:λ] = m ~ f ~ (n ~ f ~ x) }]
  NumEq[N2, PLUS ~ N2 ~ N0]
  NumEq[N2, PLUS ~ N1 ~ N1]
  NumEq[N3, PLUS ~ N1 ~ N2]
  NumEq[N3, PLUS ~ N2 ~ N1]

  type Clo1[r<:λ] = λ1[λF1 { type ap[_<:λ] = r }]
  type PRED_GH[f<:λ] = λ2[λF2 { type ap[g<:λ,h<:λ] = h ~ (g ~ f) }]
  type PRED = λ3[λF3 { type ap[n<:λ,f<:λ,x<:λ] = n ~ PRED_GH[f] ~ Clo1[x] ~ I }]
  NumEq[N2, PRED ~ N3]
  NumEq[N1, PRED ~ N2]
  NumEq[N0, PRED ~ N1]

  // NOTE: Negative numbers all stay 0
  type MINUS = λ2[λF2 { type ap[m<:λ,n<:λ] = (n ~ PRED) ~ m }]
  NumEq[N2, MINUS ~ N2 ~ N0]
  NumEq[N1, MINUS ~ N2 ~ N1]
  NumEq[N0, MINUS ~ N2 ~ N2]
  NumEq[N0, MINUS ~ N0 ~ N0]

  type NUMEQ = λ2[λF2 { type ap[m<:λ,n<:λ] = And ~ (ISZERO ~ (MINUS ~ m ~ n)) ~ (ISZERO ~ (MINUS ~ n ~ m)) }]
  Eq[T, NUMEQ ~ N0 ~ N0]
  Eq[T, NUMEQ ~ N1 ~ N1]
  Eq[T, NUMEQ ~ N2 ~ N2]
  Eq[F, NUMEQ ~ N1 ~ N0]
  Eq[F, NUMEQ ~ N1 ~ N2]
  Eq[F, NUMEQ ~ N0 ~ N1]
  Eq[F, NUMEQ ~ N2 ~ N1]

  // type IFNUMEQ = λ4[λF4 { type ap[m<:λ,n<:λ,t<:λ,f<:λ] = IF ~ (NUMEQ ~ m ~ n) ~ t ~ f }]

  // ====================================================================================================================
  // Enforcing exclusive disjunction (A or B but not both)

  /*
  Env *- debug[b]
  Capability *- risk score  = failure + DB+2 + out+3 (0-10)
  Capability *- connect to outside
  Capability *- connect to DB
  Capability *- impact failure [0-5]
  Capability
  */

  trait Env {
    type Debug <: λ
  }

  trait Capability {
    type ConnectsToOutside <: λ
    type ConnectsToDB <: λ
    type ImpactFailure <: λ
    final type RiskScore = PLUS ~ (If ~ ConnectsToOutside ~ N3 ~ N0) ~ (PLUS ~ (If ~ ConnectsToDB ~ N2 ~ N0) ~ ImpactFailure)
  }

  trait BalanceCalc extends Capability {
    override type ConnectsToOutside = F
    override type ConnectsToDB = T
    override type ImpactFailure = N4
  }

  trait MemCheck extends Capability {
    override type ConnectsToOutside = F
    override type ConnectsToDB = F
    override type ImpactFailure = N0
  }

  trait RequestStmt extends Capability {
    override type ConnectsToOutside = T
    override type ConnectsToDB = F
    override type ImpactFailure = N1
  }

  trait Module {
    //type Capabilities <: HList of Capability
  }

  object DoesHeaps {

  }

  /*
  trait OMG{ type ImpactFailure <: V forSome {type V <: λ; type Check <: NUMEQ ~ V ~ N2 } }
  new OMG{type ImpactFailure = N3}
  */
}
