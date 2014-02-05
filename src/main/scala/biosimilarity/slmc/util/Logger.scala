package biosimilarity.slmc.util

class Logger() {
  private var logroll = ""
  def getLog = logroll
  def log(msg: String) = 
    logroll = logroll + msg
  def logln(msg: String) =
    log(msg + "\n")
}