import scalaz.std.either._
import scalaz.std.list._
import scalaz.syntax.traverse._

object Existentials {

  trait SurveyType { self =>
    type Question
    type Answer

    val jsonTypeId: String

    val questionToJson: Question => Json
    val questionFromJson: Json => Json.ParseResult[Question]

    val answerToJson: Answer => Json
    val answerFromJson: Json => Json.ParseResult[Answer]

    val askUser: Question => IO[Answer]

    final type AndQuestion = SurveyType.AndQuestion { val surveyType: self.type }
    final def AndQuestion(q: Question): self.AndQuestion =
      new SurveyType.AndQuestion {
        override val surveyType: self.type = self
        override val question = q
      }
  }

    object FreeText extends SurveyType {
      override type Question        = String
      override type Answer          = String
      override val jsonTypeId       = "text"
      override val questionToJson   = Json.Str
      override val questionFromJson = _.stringValue
      override val answerToJson     = Json.Str
      override val answerFromJson   = _.stringValue
      override val askUser          = ??? // exercise to the reader
    }

    object MultipleChoice extends SurveyType {
      override type Question      = (String, NonEmptyList[String])
      override type Answer        = Int
      override val jsonTypeId     = "multiple-choice"
      override val answerToJson   = Json.Num(_)
      override val answerFromJson = _.intValue

      override val questionToJson = { case (question, choices) =>
        Json.Object(List(
          "question" -> Json.Str(question),
          "choices" -> Json.Array(choices.toList.map(Json.Str))
        ))
      }

      override val questionFromJson = (j: Json) => for {
        q  <- j.get("question").flatMap(_.stringValue)
        cj <- j.get("choices").flatMap(_.nonEmptyList)
        c  <- cj.traverse(_.stringValue)
      } yield (q, c)

      override val askUser = ??? // exercise to the reader
    }

    object SurveyType {

      // It'd be safer to use a macro for this. I normally use:
      // https://github.com/japgolly/microlibs-scala/blob/master/adt-macros/shared/src/main/scala/japgolly/microlibs/adt_macros/AdtMacros.scala#L18
      val values: NonEmptyList[SurveyType] =
        NonEmptyList(FreeText, MultipleChoice)

      val fromJsonType: Map[String, SurveyType] =
        values.map(t => t.jsonTypeId -> t).toMap

      // Make sure there are no duplicate jsonTypeIds
      assert(fromJsonType.size == values.size)

      trait AndQuestion {
        val surveyType: SurveyType
        val question: surveyType.Question
        final type Answer = surveyType.Answer
        final def askUser = surveyType.askUser(question)
      }
    }

  type Survey = List[SurveyType.AndQuestion]

  // ===================================================================================================================

  // Example JSON
  // [
  //   {"text": "What's your name?"},
  //   {"multiple-choice": {
  //       "Q": "How many fingers do you have?",
  //       "C": ["≤10", "≤20", ">20", "none of them", "all of them"]
  //     }
  //   },
  //   {"text": "Why are you answering this?"}
  // ]
  object UseCase1 {
    val parseJsonQuestion: Json => Json.ParseResult[SurveyType.AndQuestion] = {
      case Json.Object((key, value) :: Nil) =>
        SurveyType.fromJsonType.get(key) match {
          case Some(surveyType) => surveyType.questionFromJson(value).map(surveyType.AndQuestion)
          case None             => Json.fail(s"Unrecognised survey type: $key")
        }
      case j => Json.fail(s"JSON object with a single key-value expected; got " + j)
    }

    val parseJsonQuestions: Json.Array => Json.ParseResult[Survey] =
      _.toList.traverse(parseJsonQuestion)
  }

  object UseCase2 {
    def qaJson(q: SurveyType.AndQuestion)(a: q.Answer): Json =
      Json.Object(List(
        "type"     -> Json.Str(q.surveyType.jsonTypeId),
        "question" -> q.surveyType.questionToJson(q.question),
        "answer"   -> q.surveyType.answerToJson(a)
      ))

    def executeSurvey(qs: Survey): IO[Json.Array] =
      qs.traverse(q => q.askUser.map(qaJson(q))).map(Json.Array)
  }

  object SpecificExample {
    // Specific use
    def welcomePage: IO[Unit] = {
      val q1 = FreeText.AndQuestion("What's your name?")

      val ageRanges = NonEmptyList("0-30", "31-60", "61+")
      val q2 = MultipleChoice.AndQuestion(("How old are you?", ageRanges))

      for {
        name     <- q1.askUser
        ageIndex <- q2.askUser
        ageRange  = ageRanges(ageIndex)
        _        <- IO(println(s"Hello $name, you are $ageRange years old."))
      } yield ()
    }
  }
}
