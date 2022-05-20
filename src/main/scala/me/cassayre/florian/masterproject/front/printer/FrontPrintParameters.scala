package me.cassayre.florian.masterproject.front.printer

import me.cassayre.florian.masterproject.front.parser.FrontSymbols

private[printer] case class FrontPrintParameters(s: FrontSymbols, symbols: FrontPrintStyle, compact: Boolean) {
  //export S.*
}

private[printer] object FrontPrintParameters {
  def apply(symbols: FrontPrintStyle, compact: Boolean): FrontPrintParameters = {
    val s = symbols match {
      case FrontPrintStyle.Ascii => FrontSymbols.FrontAsciiSymbols
      case FrontPrintStyle.Unicode => FrontSymbols.FrontUnicodeSymbols
      case FrontPrintStyle.Latex => FrontSymbols.FrontLatexSymbols
    }
    FrontPrintParameters(s, symbols, compact)
  }
}
