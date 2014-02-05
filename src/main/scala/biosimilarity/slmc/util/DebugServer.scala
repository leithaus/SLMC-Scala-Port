package biosimilarity.slmc.util

import com.sun.net.httpserver._
import java.net.InetSocketAddress
import biosimilarity.slmc.ast.parsing._
import biosimilarity.slmc.ast.sr.ParseError
import biosimilarity.slmc.SLMC
import biosimilarity.slmc.Evaluator

trait Server {
  
  var port = 8080
  
  val responseCodes = Map("200" -> 200, "404" -> 404)
  val mimeTypes = Map("html" -> "text/html", "png" -> "image/png")
  val Page404 = <html><head><title>Page Not Found</title></head><body><p>Sorry but that resource does not exist</p></body></html>
  
  var routes: List[(String, HttpHandler)] = Nil
  
  def register(route:String)(handle_f: HttpExchange => Unit) {
    object handler extends HttpHandler {
      def handle(exchange: HttpExchange) {
        handle_f(exchange)
      }
    }
    routes = (route, handler)::routes
  }
  
  def start() {
    println("Server spinning up.")
    val server = HttpServer.create(new InetSocketAddress(port), 10)
    routes.foreach({ case (route, handler) => server.createContext(route, handler) })
    server.start
    Console.println("Press return to stop the server")
    while (Console.readLine() == null) {}
    server.stop(0)
  }
}

object DebugServer extends Server {
  
  var environment: Option[SLMC] = None
  
  def setPersistence: Boolean => Unit = {
    case true =>
      environment = Some(environment.getOrElse(new SLMC))
    case false =>
      environment = None
  }
  
  def handle(exchange: HttpExchange) {
    import java.io._
    import java.nio._
    import scala.io.Source
	  
    println("Got a request!")
    var env = environment.getOrElse(new SLMC)
    try {
	
	    val headers = new java.util.ArrayList[String]()
	    headers.add("text/html")
	    exchange.getResponseHeaders.put("Content-Type: ", headers)
	    exchange.sendResponseHeaders(200, 0)
	    
	    val out = new PrintWriter(exchange.getResponseBody())
	    
	    for(command <- Parser.fromInputStream(exchange.getRequestBody())) {
	      val (newEnv, response) = Evaluator(env, command)
	      env = newEnv
	      out.println(response)
	    }
	    
    } catch {
      case e: Throwable => 
        println("got an except " + e.toString())
        e.printStackTrace()
    } finally {
	    exchange.close()
	    if(environment.isDefined) {
	      environment = Some(env)
	    }
    }
  }  

}