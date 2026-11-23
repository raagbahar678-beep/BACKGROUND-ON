package com.example.myapp

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.Context
import android.content.Intent
import android.content.MutableContextWrapper
import android.content.pm.PackageManager
import android.content.res.ColorStateList
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.drawable.Drawable
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.IBinder
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.provider.Settings
import android.text.InputType
import android.text.TextUtils
import android.view.Gravity
import android.view.InputDevice
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.webkit.CookieManager
import android.webkit.JsPromptResult
import android.webkit.JsResult
import android.webkit.RenderProcessGoneDetail
import android.webkit.ValueCallback
import android.webkit.WebChromeClient
import android.webkit.WebResourceError
import android.webkit.WebResourceRequest
import android.webkit.WebSettings
import android.webkit.WebView
import android.webkit.WebViewClient
import android.widget.Button
import android.widget.CheckBox
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.TextView
import android.widget.Toast
import org.json.JSONArray
import org.json.JSONObject
import kotlin.math.ceil
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sqrt

private const val MAX_APPS = 20
private const val PREFS = "alive_apps"
private const val REQ_FILE = 41
private const val REQ_NOTIF = 42
private const val MP = ViewGroup.LayoutParams.MATCH_PARENT
private const val WC = ViewGroup.LayoutParams.WRAP_CONTENT
private const val CHANNEL_ID = "alive_apps_keepalive"
private const val NOTIF_ID = 7

object Col {
    val BG: Int = Color.parseColor("#0F1317")
    val BAR: Int = Color.parseColor("#171D24")
    val BTN: Int = Color.parseColor("#2B3846")
    val CHIP: Int = Color.parseColor("#252F3B")
    val SEL: Int = Color.parseColor("#1F6FD6")
    val DIM: Int = Color.parseColor("#9AA7B5")
    val HDR: Int = Color.parseColor("#2A3441")
    val PROG: Int = Color.parseColor("#4FC3F7")
}

fun dpOf(ctx: Context, v: Int): Int = (v * ctx.resources.displayMetrics.density + 0.5f).toInt()

private fun onOff(b: Boolean): String = if (b) "ON" else "OFF"

private fun normalizeUrl(raw: String): String {
    val t = raw.trim()
    if (t.isEmpty()) return ""
    val lower = t.lowercase()
    if (lower.startsWith("http://") || lower.startsWith("https://")) return t
    if (t.contains(" ") || !t.contains(".")) return "https://www.google.com/search?q=" + Uri.encode(t)
    return "https://" + t
}

private fun hostOf(url: String): String {
    var h: String? = null
    try {
        h = Uri.parse(url).host
    } catch (e: Exception) {
    }
    val s = h ?: url
    return if (s.startsWith("www.")) s.substring(4) else s
}

class Preset(val name: String, val url: String, val desktop: Boolean)

private val PRESETS: List<Preset> = listOf(
    Preset("WhatsApp Web", "https://web.whatsapp.com", true),
    Preset("Gmail", "https://mail.google.com", false),
    Preset("YouTube", "https://m.youtube.com", false),
    Preset("Google", "https://www.google.com", false),
    Preset("Google Maps", "https://www.google.com/maps", false),
    Preset("Google Drive", "https://drive.google.com", false),
    Preset("Google Calendar", "https://calendar.google.com", false),
    Preset("Google Docs", "https://docs.google.com", false),
    Preset("Google Meet", "https://meet.google.com", false),
    Preset("Google News", "https://news.google.com", false),
    Preset("Telegram", "https://web.telegram.org/k/", false),
    Preset("Facebook", "https://m.facebook.com", false),
    Preset("Instagram", "https://www.instagram.com", false),
    Preset("X (Twitter)", "https://x.com", false),
    Preset("LinkedIn", "https://www.linkedin.com", false),
    Preset("Reddit", "https://www.reddit.com", false),
    Preset("GitHub", "https://github.com", false),
    Preset("Wikipedia", "https://www.wikipedia.org", false),
    Preset("ChatGPT", "https://chatgpt.com", false),
    Preset("Claude", "https://claude.ai", false),
    Preset("Outlook", "https://outlook.live.com", false),
    Preset("Slack", "https://app.slack.com", false),
    Preset("Discord", "https://discord.com/app", false),
    Preset("Spotify", "https://open.spotify.com", false),
    Preset("Amazon", "https://www.amazon.com", false)
)

class AppEntry(val id: Int, var name: String, var url: String, var desktop: Boolean) {
    var curUrl: String = url
    var title: String = ""
    var progress: Int = 100
    var web: WebView? = null
    var cw: MutableContextWrapper? = null
    var failedAt: Long = 0L
    var retries: Int = 0
    var hadError: Boolean = false
}

// Process-wide holder: the WebViews live here, so they survive the Activity being recreated.
object Hub {
    val apps = ArrayList<AppEntry>()
    val main = Handler(Looper.getMainLooper())
    var appCtx: Context? = null
    var ui: MainActivity? = null
    var visible = false
    var loaded = false
    var selected = 0
    var grid = false
    var cols = 0
    var keepScreen = true
    var keepBg = true
    var confirmClose = true
    var throttle = false
    var firstRun = true
    var askedNotif = false
    var nextId = 1
    var mobileUa = ""
    var desktopUa = ""
    private var lastSave = 0L

    private val tick: Runnable = object : Runnable {
        override fun run() {
            healAndSave()
            main.postDelayed(this, 10000L)
        }
    }

    fun start(ctx: Context) {
        if (loaded) return
        loaded = true
        val c = ctx.applicationContext
        appCtx = c
        var def = ""
        try {
            def = WebSettings.getDefaultUserAgent(c)
        } catch (e: Exception) {
        }
        mobileUa = def.replace("; wv)", ")").replace(" Version/4.0", "")
        val m = Regex("Chrome/([0-9.]+)").find(def)
        val ver = if (m != null) m.groupValues[1] else "124.0.0.0"
        desktopUa = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/" + ver + " Safari/537.36"
        val p = c.getSharedPreferences(PREFS, Context.MODE_PRIVATE)
        keepScreen = p.getBoolean("keepScreen", true)
        keepBg = p.getBoolean("keepBg", true)
        confirmClose = p.getBoolean("confirmClose", true)
        throttle = p.getBoolean("throttle", false)
        grid = p.getBoolean("grid", false)
        cols = p.getInt("cols", 0)
        selected = p.getInt("selected", 0)
        firstRun = p.getBoolean("firstRun", true)
        askedNotif = p.getBoolean("askedNotif", false)
        nextId = p.getInt("nextId", 1)
        try {
            val arr = JSONArray(p.getString("apps", "[]") ?: "[]")
            val count = min(arr.length(), MAX_APPS)
            for (i in 0 until count) {
                val o = arr.getJSONObject(i)
                val a = AppEntry(nextId, o.optString("n", "App"), o.optString("u", "about:blank"), o.optBoolean("d", false))
                nextId++
                a.curUrl = o.optString("c", a.url)
                apps.add(a)
            }
        } catch (e: Exception) {
        }
        if (selected < 0 || selected >= apps.size) selected = 0
        for (a in apps) createWeb(a)
        val sel = apps.getOrNull(selected)
        if (sel != null) loadLater(sel, 0L)
        var delay = 0L
        for (a in apps) {
            if (a !== sel) {
                delay += 450L
                loadLater(a, delay)
            }
        }
        main.postDelayed(tick, 10000L)
    }

    fun toastApp(msg: String) {
        val c = appCtx ?: return
        Toast.makeText(c, msg, Toast.LENGTH_SHORT).show()
    }

    fun openExternal(url: String) {
        val c = appCtx ?: return
        try {
            val i: Intent
            if (url.startsWith("intent:")) {
                i = Intent.parseUri(url, Intent.URI_INTENT_SCHEME)
                i.addCategory(Intent.CATEGORY_BROWSABLE)
                i.setComponent(null)
                i.setSelector(null)
            } else {
                i = Intent(Intent.ACTION_VIEW, Uri.parse(url))
            }
            i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            c.startActivity(i)
        } catch (e: Exception) {
            toastApp("Can't open this link")
        }
    }

    fun applyUa(w: WebView, desktop: Boolean) {
        w.settings.userAgentString = if (desktop) desktopUa else mobileUa
    }

    fun createWeb(a: AppEntry): WebView {
        val base: Context = ui ?: requireNotNull(appCtx)
        val cw = MutableContextWrapper(base)
        a.cw = cw
        val w = WebView(cw)
        w.setBackgroundColor(Color.WHITE)
        val s = w.settings
        s.javaScriptEnabled = true
        s.domStorageEnabled = true
        s.mediaPlaybackRequiresUserGesture = false
        s.useWideViewPort = true
        s.loadWithOverviewMode = true
        s.setSupportZoom(true)
        s.builtInZoomControls = true
        s.displayZoomControls = false
        s.javaScriptCanOpenWindowsAutomatically = true
        s.allowFileAccess = false
        s.mixedContentMode = WebSettings.MIXED_CONTENT_COMPATIBILITY_MODE
        applyUa(w, a.desktop)
        val cm = CookieManager.getInstance()
        cm.setAcceptCookie(true)
        cm.setAcceptThirdPartyCookies(w, true)
        w.setRendererPriorityPolicy(WebView.RENDERER_PRIORITY_IMPORTANT, false)
        w.setDownloadListener { url, _, _, _, _ ->
            if (url != null && url.startsWith("http")) openExternal(url) else toastApp("This file type can't be downloaded here")
        }
        w.setOnTouchListener { _, ev ->
            if (ev.actionMasked == MotionEvent.ACTION_DOWN) Hub.ui?.onWebTouched(a)
            false
        }
        w.webViewClient = object : WebViewClient() {
            override fun shouldOverrideUrlLoading(view: WebView?, request: WebResourceRequest?): Boolean {
                val u = request?.url ?: return false
                val sch = u.scheme ?: return false
                if (sch == "http" || sch == "https" || sch == "about" || sch == "data" || sch == "blob" || sch == "javascript" || sch == "file") return false
                openExternal(u.toString())
                return true
            }

            override fun onPageStarted(view: WebView?, url: String?, favicon: Bitmap?) {
                a.hadError = false
                a.progress = 0
                if (url != null && (url.startsWith("http://") || url.startsWith("https://"))) a.curUrl = url
                Hub.ui?.onAppProgress(a)
            }

            override fun onPageFinished(view: WebView?, url: String?) {
                if (url != null && (url.startsWith("http://") || url.startsWith("https://"))) a.curUrl = url
                if (!a.hadError) {
                    a.retries = 0
                    a.failedAt = 0L
                }
                a.progress = 100
                Hub.ui?.onAppProgress(a)
            }

            override fun onReceivedError(view: WebView?, request: WebResourceRequest?, error: WebResourceError?) {
                if (request == null || !request.isForMainFrame) return
                val code = if (error != null) error.errorCode else 0
                if (code == WebViewClient.ERROR_HOST_LOOKUP || code == WebViewClient.ERROR_CONNECT ||
                    code == WebViewClient.ERROR_IO || code == WebViewClient.ERROR_TIMEOUT
                ) {
                    a.hadError = true
                    a.failedAt = SystemClock.elapsedRealtime()
                }
            }

            override fun onRenderProcessGone(view: WebView?, detail: RenderProcessGoneDetail?): Boolean {
                renderGone(a, view)
                return true
            }
        }
        w.webChromeClient = object : WebChromeClient() {
            override fun onProgressChanged(view: WebView?, newProgress: Int) {
                a.progress = newProgress
                Hub.ui?.onAppProgress(a)
            }

            override fun onReceivedTitle(view: WebView?, title: String?) {
                a.title = title ?: ""
                Hub.ui?.onAppProgress(a)
            }

            override fun onShowFileChooser(
                webView: WebView?,
                filePathCallback: ValueCallback<Array<Uri>>?,
                fileChooserParams: WebChromeClient.FileChooserParams?
            ): Boolean {
                val act = Hub.ui
                if (act == null || filePathCallback == null || fileChooserParams == null) {
                    if (filePathCallback != null) filePathCallback.onReceiveValue(null)
                    return true
                }
                return act.pickFiles(filePathCallback, fileChooserParams)
            }

            override fun onJsAlert(view: WebView?, url: String?, message: String?, result: JsResult?): Boolean {
                return jsAlert(message, result)
            }

            override fun onJsConfirm(view: WebView?, url: String?, message: String?, result: JsResult?): Boolean {
                return jsConfirm(message, result)
            }

            override fun onJsPrompt(view: WebView?, url: String?, message: String?, defaultValue: String?, result: JsPromptResult?): Boolean {
                return jsPrompt(message, defaultValue, result)
            }
        }
        a.web = w
        return w
    }

    fun jsAlert(message: String?, result: JsResult?): Boolean {
        if (result == null) return true
        val act = ui
        if (act == null || !visible || act.isFinishing) {
            result.cancel()
            return true
        }
        AlertDialog.Builder(act)
            .setMessage(message ?: "")
            .setPositiveButton("OK") { _, _ -> result.confirm() }
            .setOnCancelListener { result.cancel() }
            .show()
        return true
    }

    fun jsConfirm(message: String?, result: JsResult?): Boolean {
        if (result == null) return true
        val act = ui
        if (act == null || !visible || act.isFinishing) {
            result.cancel()
            return true
        }
        AlertDialog.Builder(act)
            .setMessage(message ?: "")
            .setPositiveButton("OK") { _, _ -> result.confirm() }
            .setNegativeButton("Cancel") { _, _ -> result.cancel() }
            .setOnCancelListener { result.cancel() }
            .show()
        return true
    }

    fun jsPrompt(message: String?, def: String?, result: JsPromptResult?): Boolean {
        if (result == null) return true
        val act = ui
        if (act == null || !visible || act.isFinishing) {
            result.cancel()
            return true
        }
        val et = EditText(act)
        et.setText(def ?: "")
        AlertDialog.Builder(act)
            .setMessage(message ?: "")
            .setView(et)
            .setPositiveButton("OK") { _, _ -> result.confirm(et.text.toString()) }
            .setNegativeButton("Cancel") { _, _ -> result.cancel() }
            .setOnCancelListener { result.cancel() }
            .show()
        return true
    }

    fun loadLater(a: AppEntry, delayMs: Long) {
        if (delayMs <= 0L) {
            a.web?.loadUrl(a.curUrl)
            return
        }
        main.postDelayed({
            val w = a.web
            if (w != null && apps.contains(a)) w.loadUrl(a.curUrl)
        }, delayMs)
    }

    fun addApp(name: String, url: String, desktop: Boolean, delayMs: Long): AppEntry? {
        if (apps.size >= MAX_APPS) return null
        val a = AppEntry(nextId, name, url, desktop)
        nextId++
        apps.add(a)
        createWeb(a)
        loadLater(a, delayMs)
        return a
    }

    fun destroyWeb(a: AppEntry, blank: Boolean) {
        val w = a.web ?: return
        a.web = null
        try {
            (w.parent as? ViewGroup)?.removeView(w)
            w.stopLoading()
            if (blank) w.loadUrl("about:blank")
            w.destroy()
        } catch (e: Exception) {
        }
    }

    fun closeApp(a: AppEntry) {
        val i = apps.indexOf(a)
        if (i < 0) return
        destroyWeb(a, true)
        apps.removeAt(i)
        if (i < selected) selected--
        if (selected >= apps.size) selected = max(0, apps.size - 1)
        save()
    }

    // The renderer process died (usually out of memory): rebuild that app's WebView instead of crashing.
    fun renderGone(a: AppEntry, view: WebView?) {
        main.post {
            if (a.web === view && apps.contains(a)) {
                destroyWeb(a, false)
                createWeb(a)
                a.web?.loadUrl(a.curUrl)
                ui?.refreshStructure()
            }
        }
    }

    fun attachContext(act: Context) {
        for (a in apps) a.cw?.setBaseContext(act)
    }

    fun detachContext() {
        val c = appCtx ?: return
        for (a in apps) a.cw?.setBaseContext(c)
    }

    fun save() {
        val c = appCtx ?: return
        val arr = JSONArray()
        for (a in apps) {
            val cur: String? = a.web?.url
            if (cur != null && (cur.startsWith("http://") || cur.startsWith("https://"))) a.curUrl = cur
            val o = JSONObject()
            o.put("n", a.name)
            o.put("u", a.url)
            o.put("c", a.curUrl)
            o.put("d", a.desktop)
            arr.put(o)
        }
        c.getSharedPreferences(PREFS, Context.MODE_PRIVATE).edit()
            .putString("apps", arr.toString())
            .putInt("selected", selected)
            .putBoolean("grid", grid)
            .putInt("cols", cols)
            .putBoolean("keepScreen", keepScreen)
            .putBoolean("keepBg", keepBg)
            .putBoolean("confirmClose", confirmClose)
            .putBoolean("throttle", throttle)
            .putBoolean("firstRun", firstRun)
            .putBoolean("askedNotif", askedNotif)
            .putInt("nextId", nextId)
            .apply()
    }

    // Every 10 s: retry pages that failed because the network was down, and save the session every 30 s.
    private fun healAndSave() {
        val now = SystemClock.elapsedRealtime()
        for (a in apps) {
            val w = a.web ?: continue
            if (a.failedAt > 0L) {
                val wait = 20000L * (1 shl min(a.retries, 4)).toLong()
                if (now - a.failedAt >= wait) {
                    a.retries++
                    a.failedAt = 0L
                    a.hadError = false
                    try {
                        w.reload()
                    } catch (e: Exception) {
                    }
                }
            }
        }
        if (now - lastSave >= 30000L) {
            lastSave = now
            save()
        }
    }
}

class ProgBar(ctx: Context) : View(ctx) {
    private val paint = Paint()
    var value: Int = 0
        set(v) {
            field = v
            invalidate()
        }

    init {
        paint.color = Col.PROG
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val w = width * value / 100f
        canvas.drawRect(0f, 0f, w, height.toFloat(), paint)
    }
}

class TabStrip(ctx: Context) : HorizontalScrollView(ctx) {
    override fun onGenericMotionEvent(ev: MotionEvent): Boolean {
        if (ev.actionMasked == MotionEvent.ACTION_SCROLL && (ev.source and InputDevice.SOURCE_CLASS_POINTER) != 0) {
            val v = ev.getAxisValue(MotionEvent.AXIS_VSCROLL)
            if (v != 0f) {
                scrollBy((-v * 140f).toInt(), 0)
                return true
            }
        }
        return super.onGenericMotionEvent(ev)
    }
}

class Tile(ctx: Context, val app: AppEntry) : LinearLayout(ctx) {
    val header = LinearLayout(ctx)
    val title = TextView(ctx)
    val closeBtn = TextView(ctx)
    var web: WebView? = null

    init {
        orientation = LinearLayout.VERTICAL
        header.orientation = LinearLayout.HORIZONTAL
        header.gravity = Gravity.CENTER_VERTICAL
        title.text = app.name
        title.textSize = 11f
        title.setTextColor(Color.WHITE)
        title.setSingleLine(true)
        title.ellipsize = TextUtils.TruncateAt.END
        title.gravity = Gravity.CENTER_VERTICAL
        title.setPadding(dpOf(ctx, 6), 0, dpOf(ctx, 4), 0)
        closeBtn.text = "×"
        closeBtn.textSize = 17f
        closeBtn.setTextColor(Color.WHITE)
        closeBtn.gravity = Gravity.CENTER
        closeBtn.setPadding(dpOf(ctx, 9), 0, dpOf(ctx, 9), 0)
        header.addView(title, LinearLayout.LayoutParams(0, MP, 1f))
        header.addView(closeBtn, LinearLayout.LayoutParams(WC, MP))
        addView(header, LinearLayout.LayoutParams(MP, dpOf(ctx, 26)))
        header.visibility = View.GONE
    }

    fun attachWeb(w: WebView) {
        (w.parent as? ViewGroup)?.removeView(w)
        addView(w, LinearLayout.LayoutParams(MP, 0, 1f))
        web = w
    }

    fun releaseWeb() {
        val w = web ?: return
        if (w.parent === this) removeView(w)
        web = null
    }

    fun setGridMode(grid: Boolean, selected: Boolean) {
        header.visibility = if (grid) View.VISIBLE else View.GONE
        header.setBackgroundColor(if (selected) Col.SEL else Col.HDR)
        title.text = app.name
    }
}

// Lays out all tiles itself. Tabs mode: the selected tile fills the area and the others are parked
// just off-screen (still attached and visible, so they never pause). Grid mode: every tile is on screen.
class TileHost(ctx: Context) : ViewGroup(ctx) {
    var grid = false
    var cols = 0
    var order: List<View> = ArrayList<View>()
    var selectedView: View? = null

    private fun colsFor(n: Int, w: Int, h: Int): Int {
        if (n <= 1) return 1
        if (cols > 0) return min(cols, n)
        val ratio = if (h > 0) w.toFloat() / h.toFloat() else 1f
        val c = ceil(sqrt((n * ratio).toDouble())).toInt()
        return max(1, min(c, n))
    }

    override fun onMeasure(widthMeasureSpec: Int, heightMeasureSpec: Int) {
        val w = View.MeasureSpec.getSize(widthMeasureSpec)
        val h = View.MeasureSpec.getSize(heightMeasureSpec)
        setMeasuredDimension(w, h)
        val n = order.size
        if (n == 0) return
        var cw = w
        var ch = h
        if (grid) {
            val c = colsFor(n, w, h)
            val rows = (n + c - 1) / c
            cw = max(1, w / c)
            ch = max(1, h / rows)
        }
        val ws = View.MeasureSpec.makeMeasureSpec(cw, View.MeasureSpec.EXACTLY)
        val hs = View.MeasureSpec.makeMeasureSpec(ch, View.MeasureSpec.EXACTLY)
        for (v in order) v.measure(ws, hs)
    }

    override fun onLayout(changed: Boolean, l: Int, t: Int, r: Int, b: Int) {
        val w = r - l
        val h = b - t
        val n = order.size
        if (n == 0) return
        if (grid) {
            val c = colsFor(n, w, h)
            val rows = (n + c - 1) / c
            val cw = max(1, w / c)
            val ch = max(1, h / rows)
            for ((i, v) in order.withIndex()) {
                val x = (i % c) * cw
                val y = (i / c) * ch
                v.layout(x, y, x + cw, y + ch)
            }
        } else {
            for (v in order) {
                if (v === selectedView) v.layout(0, 0, w, h) else v.layout(-w, 0, 0, h)
            }
        }
    }
}

class KeepAliveService : Service() {
    private var wake: PowerManager.WakeLock? = null

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        val nm = getSystemService(NotificationManager::class.java)
        nm.createNotificationChannel(NotificationChannel(CHANNEL_ID, "Keep apps alive", NotificationManager.IMPORTANCE_LOW))
        val open = Intent(this, MainActivity::class.java)
        open.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_SINGLE_TOP)
        val pi = PendingIntent.getActivity(this, 0, open, PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT)
        val n = Notification.Builder(this, CHANNEL_ID)
            .setSmallIcon(android.R.drawable.ic_dialog_info)
            .setContentTitle("Alive Apps is running")
            .setContentText(Hub.apps.size.toString() + " apps are kept alive. Tap to open.")
            .setContentIntent(pi)
            .setOngoing(true)
            .build()
        try {
            startForeground(NOTIF_ID, n)
        } catch (e: Exception) {
            stopSelf()
            return START_NOT_STICKY
        }
        if (Hub.keepBg) acquireWake() else releaseWake()
        return START_NOT_STICKY
    }

    private fun acquireWake() {
        if (wake == null) {
            val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
            val wl = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "AliveApps:keepalive")
            wl.setReferenceCounted(false)
            wl.acquire()
            wake = wl
        }
    }

    private fun releaseWake() {
        val w = wake
        if (w != null && w.isHeld) w.release()
        wake = null
    }

    override fun onDestroy() {
        releaseWake()
        super.onDestroy()
    }
}

class MainActivity : Activity() {

    private lateinit var host: TileHost
    private lateinit var strip: LinearLayout
    private lateinit var stripScroll: TabStrip
    private lateinit var statusView: TextView
    private lateinit var progView: ProgBar
    private lateinit var emptyView: TextView
    private lateinit var btnGrid: Button
    private val tiles = ArrayList<Tile>()
    private val chips = HashMap<Int, LinearLayout>()
    private var swallowKey = -1
    var pendingFile: ValueCallback<Array<Uri>>? = null

    private fun dp(v: Int): Int = dpOf(this, v)

    private fun toast(msg: String) {
        Toast.makeText(this, msg, Toast.LENGTH_SHORT).show()
    }

    // ---------------- lifecycle ----------------

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Hub.ui = this
        Hub.start(this)
        Hub.attachContext(this)
        buildUi()
        syncTiles()
        rebuildStrip()
        applyLayoutState()
        applyKeepScreen()
        updateService()
        startupPrompts()
    }

    override fun onResume() {
        super.onResume()
        Hub.visible = true
        for (a in Hub.apps) a.web?.onResume()
        applyKeepScreen()
        updateService()
    }

    override fun onPause() {
        Hub.visible = false
        Hub.save()
        CookieManager.getInstance().flush()
        super.onPause()
    }

    override fun onDestroy() {
        for (t in tiles) t.releaseWeb()
        tiles.clear()
        Hub.detachContext()
        if (Hub.ui === this) Hub.ui = null
        val cb = pendingFile
        pendingFile = null
        if (cb != null) cb.onReceiveValue(null)
        super.onDestroy()
    }

    // Back never closes anything: it goes back inside the page, otherwise just hides the app.
    @Suppress("DEPRECATION", "OVERRIDE_DEPRECATION")
    override fun onBackPressed() {
        val w = currentApp()?.web
        if (w != null && w.canGoBack()) w.goBack() else moveTaskToBack(true)
    }

    @Suppress("DEPRECATION")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode == REQ_FILE) {
            val cb = pendingFile
            pendingFile = null
            if (cb != null) {
                var res: Array<Uri>? = null
                try {
                    res = WebChromeClient.FileChooserParams.parseResult(resultCode, data)
                } catch (e: Exception) {
                }
                cb.onReceiveValue(res)
            }
        }
    }

    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQ_NOTIF) maybeShowPresets()
    }

    // ---------------- keyboard ----------------

    override fun dispatchKeyEvent(ev: KeyEvent): Boolean {
        val code = ev.keyCode
        if (ev.action == KeyEvent.ACTION_UP && code == swallowKey) {
            swallowKey = -1
            return true
        }
        if (ev.action == KeyEvent.ACTION_DOWN) {
            val ctrl = ev.isCtrlPressed
            val alt = ev.isAltPressed
            val shift = ev.isShiftPressed
            val handled: Boolean = when {
                code == KeyEvent.KEYCODE_F5 || (ctrl && code == KeyEvent.KEYCODE_R) -> {
                    reloadCurrent()
                    true
                }
                ctrl && code == KeyEvent.KEYCODE_T -> {
                    showEditDialog(null)
                    true
                }
                ctrl && code == KeyEvent.KEYCODE_W -> {
                    closeCurrent()
                    true
                }
                ctrl && code == KeyEvent.KEYCODE_G -> {
                    toggleGrid()
                    true
                }
                ctrl && code == KeyEvent.KEYCODE_M -> {
                    showMore()
                    true
                }
                ctrl && code == KeyEvent.KEYCODE_TAB -> {
                    selectIndex(Hub.selected + (if (shift) -1 else 1))
                    true
                }
                ctrl && code == KeyEvent.KEYCODE_PAGE_DOWN -> {
                    selectIndex(Hub.selected + 1)
                    true
                }
                ctrl && code == KeyEvent.KEYCODE_PAGE_UP -> {
                    selectIndex(Hub.selected - 1)
                    true
                }
                (ctrl || alt) && code >= KeyEvent.KEYCODE_1 && code <= KeyEvent.KEYCODE_9 -> {
                    val idx = code - KeyEvent.KEYCODE_1
                    if (idx < Hub.apps.size) selectIndex(idx)
                    true
                }
                alt && code == KeyEvent.KEYCODE_DPAD_LEFT -> {
                    val w = currentApp()?.web
                    if (w != null && w.canGoBack()) w.goBack()
                    true
                }
                alt && code == KeyEvent.KEYCODE_DPAD_RIGHT -> {
                    val w = currentApp()?.web
                    if (w != null && w.canGoForward()) w.goForward()
                    true
                }
                else -> false
            }
            if (handled) {
                swallowKey = code
                return true
            }
        }
        return super.dispatchKeyEvent(ev)
    }

    // ---------------- UI construction ----------------

    private fun rippleBg(color: Int, radiusDp: Int): Drawable {
        val gd = GradientDrawable()
        gd.setColor(color)
        gd.cornerRadius = dp(radiusDp).toFloat()
        return RippleDrawable(ColorStateList.valueOf(0x44FFFFFF), gd, null)
    }

    private fun toolBtn(text: String, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.setAllCaps(false)
        b.textSize = 13f
        b.setTextColor(Color.WHITE)
        b.minWidth = 0
        b.minHeight = 0
        b.minimumWidth = 0
        b.minimumHeight = 0
        b.setPadding(dp(2), 0, dp(2), 0)
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        b.stateListAnimator = null
        b.background = rippleBg(Col.BTN, 8)
        b.setOnClickListener { onClick() }
        return b
    }

    private fun buildUi() {
        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setBackgroundColor(Col.BG)

        // Row 1: equal-weight toolbar buttons (never on top of the apps)
        val bar = LinearLayout(this)
        bar.orientation = LinearLayout.HORIZONTAL
        bar.setBackgroundColor(Col.BAR)
        bar.setPadding(dp(3), dp(4), dp(3), dp(4))
        val bAdd = toolBtn("+ Add") { showEditDialog(null) }
        btnGrid = toolBtn("Grid") { toggleGrid() }
        val bReload = toolBtn("Reload") { reloadCurrent() }
        val bClose = toolBtn("Close") { closeCurrent() }
        val bMore = toolBtn("More") { showMore() }
        val all = arrayOf(bAdd, btnGrid, bReload, bClose, bMore)
        for (b in all) {
            val lp = LinearLayout.LayoutParams(0, dp(42), 1f)
            lp.setMargins(dp(2), 0, dp(2), 0)
            bar.addView(b, lp)
        }
        root.addView(bar, LinearLayout.LayoutParams(MP, WC))

        // Row 2: tab strip with one chip per app
        stripScroll = TabStrip(this)
        stripScroll.setBackgroundColor(Col.BAR)
        stripScroll.isHorizontalScrollBarEnabled = true
        strip = LinearLayout(this)
        strip.orientation = LinearLayout.HORIZONTAL
        stripScroll.addView(strip, FrameLayout.LayoutParams(WC, MP))
        root.addView(stripScroll, LinearLayout.LayoutParams(MP, dp(42)))

        progView = ProgBar(this)
        root.addView(progView, LinearLayout.LayoutParams(MP, dp(3)))

        // Status text under the toolbar rows
        statusView = TextView(this)
        statusView.textSize = 11f
        statusView.setTextColor(Col.DIM)
        statusView.setSingleLine(true)
        statusView.ellipsize = TextUtils.TruncateAt.MIDDLE
        statusView.setPadding(dp(8), dp(2), dp(8), dp(3))
        root.addView(statusView, LinearLayout.LayoutParams(MP, WC))

        val content = FrameLayout(this)
        host = TileHost(this)
        content.addView(host, FrameLayout.LayoutParams(MP, MP))
        emptyView = TextView(this)
        emptyView.text = "No apps open yet.\n\nTap \"+ Add\" to open a website or web app,\nor More > Add popular apps."
        emptyView.setTextColor(Col.DIM)
        emptyView.textSize = 15f
        emptyView.gravity = Gravity.CENTER
        content.addView(emptyView, FrameLayout.LayoutParams(MP, MP))
        root.addView(content, LinearLayout.LayoutParams(MP, 0, 1f))

        setContentView(root)
    }

    private fun tileFor(a: AppEntry?): Tile? {
        if (a == null) return null
        for (t in tiles) {
            if (t.app === a) return t
        }
        return null
    }

    private fun currentApp(): AppEntry? = Hub.apps.getOrNull(Hub.selected)

    // Make the tiles match Hub.apps without detaching WebViews that stay open.
    private fun syncTiles() {
        val iter = tiles.iterator()
        while (iter.hasNext()) {
            val t = iter.next()
            if (!Hub.apps.contains(t.app) || t.web == null || t.web !== t.app.web) {
                t.releaseWeb()
                host.removeView(t)
                iter.remove()
            }
        }
        for (a in Hub.apps) {
            val w = a.web ?: continue
            if (tileFor(a) == null) {
                val t = Tile(this, a)
                t.attachWeb(w)
                t.title.setOnClickListener { focusApp(a) }
                t.title.setOnLongClickListener {
                    selectIndex(Hub.apps.indexOf(a))
                    showAppOptions()
                    true
                }
                t.closeBtn.setOnClickListener { requestClose(a) }
                host.addView(t)
                tiles.add(t)
            }
        }
        val sorted = ArrayList<Tile>()
        for (a in Hub.apps) {
            val t = tileFor(a)
            if (t != null) sorted.add(t)
        }
        tiles.clear()
        tiles.addAll(sorted)
        host.order = ArrayList<View>(tiles)
    }

    private fun rebuildStrip() {
        strip.removeAllViews()
        chips.clear()
        for ((i, a) in Hub.apps.withIndex()) {
            val box = LinearLayout(this)
            box.orientation = LinearLayout.HORIZONTAL
            box.gravity = Gravity.CENTER_VERTICAL
            val label = TextView(this)
            label.text = (i + 1).toString() + ". " + a.name
            label.textSize = 13f
            label.setTextColor(Color.WHITE)
            label.setSingleLine(true)
            label.ellipsize = TextUtils.TruncateAt.END
            label.maxWidth = dp(150)
            label.gravity = Gravity.CENTER_VERTICAL
            label.setPadding(dp(10), 0, dp(4), 0)
            val x = TextView(this)
            x.text = "×"
            x.textSize = 19f
            x.setTextColor(Col.DIM)
            x.gravity = Gravity.CENTER
            x.setPadding(dp(9), 0, dp(11), 0)
            box.addView(label, LinearLayout.LayoutParams(WC, MP))
            box.addView(x, LinearLayout.LayoutParams(WC, MP))
            label.setOnClickListener { selectIndex(Hub.apps.indexOf(a)) }
            label.setOnLongClickListener {
                selectIndex(Hub.apps.indexOf(a))
                showAppOptions()
                true
            }
            x.setOnClickListener { requestClose(a) }
            val lp = LinearLayout.LayoutParams(WC, MP)
            lp.setMargins(dp(2), dp(3), dp(2), dp(3))
            strip.addView(box, lp)
            chips[a.id] = box
        }
    }

    private fun applyLayoutState() {
        val sel = Hub.apps.getOrNull(Hub.selected)
        host.grid = Hub.grid
        host.cols = Hub.cols
        host.selectedView = tileFor(sel)
        for (t in tiles) {
            val isSel = t.app === sel
            t.setGridMode(Hub.grid, isSel)
            t.visibility = if (!Hub.grid && Hub.throttle && !isSel) View.INVISIBLE else View.VISIBLE
        }
        for (a in Hub.apps) {
            val c = chips[a.id] ?: continue
            c.background = rippleBg(if (a === sel) Col.SEL else Col.CHIP, 8)
        }
        stripScroll.visibility = if (Hub.grid) View.GONE else View.VISIBLE
        btnGrid.text = if (Hub.grid) "Tabs" else "Grid"
        emptyView.visibility = if (tiles.isEmpty()) View.VISIBLE else View.GONE
        updateStatus()
        host.requestLayout()
    }

    private fun updateStatus() {
        val sel = Hub.apps.getOrNull(Hub.selected)
        val sb = StringBuilder()
        sb.append("Alive: ").append(Hub.apps.size).append("/").append(MAX_APPS)
        if (Hub.grid) {
            sb.append("  |  Grid view - tap a tile title to open it")
        } else if (sel != null) {
            sb.append("  |  ").append(sel.name)
            if (sel.title.isNotEmpty()) sb.append(": ").append(sel.title)
        }
        statusView.text = sb.toString()
        val p = if (sel != null) sel.progress else 0
        progView.value = if (p >= 100) 0 else p
    }

    private fun applyKeepScreen() {
        if (Hub.keepScreen) {
            window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        } else {
            window.clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        }
    }

    private fun updateService() {
        val i = Intent(this, KeepAliveService::class.java)
        try {
            if (Hub.apps.isNotEmpty() && Hub.keepBg) {
                startForegroundService(i)
            } else {
                stopService(i)
            }
        } catch (e: Exception) {
        }
    }

    // ---------------- callbacks used by Hub ----------------

    fun onAppProgress(a: AppEntry) {
        if (a === Hub.apps.getOrNull(Hub.selected)) updateStatus()
    }

    fun onWebTouched(a: AppEntry) {
        if (!Hub.grid) return
        val i = Hub.apps.indexOf(a)
        if (i >= 0 && i != Hub.selected) {
            Hub.selected = i
            applyLayoutState()
        }
    }

    fun refreshStructure() {
        syncTiles()
        rebuildStrip()
        applyLayoutState()
    }

    fun pickFiles(cb: ValueCallback<Array<Uri>>, params: WebChromeClient.FileChooserParams): Boolean {
        val old = pendingFile
        if (old != null) old.onReceiveValue(null)
        pendingFile = cb
        try {
            @Suppress("DEPRECATION")
            startActivityForResult(params.createIntent(), REQ_FILE)
        } catch (e: Exception) {
            pendingFile = null
            cb.onReceiveValue(null)
        }
        return true
    }

    // ---------------- actions ----------------

    private fun structureChanged() {
        refreshStructure()
        updateService()
        Hub.save()
    }

    fun selectIndex(i: Int) {
        val n = Hub.apps.size
        if (n == 0) return
        Hub.selected = ((i % n) + n) % n
        applyLayoutState()
        val a = Hub.apps[Hub.selected]
        tileFor(a)?.web?.requestFocus()
        val c = chips[a.id]
        if (c != null) {
            stripScroll.post { stripScroll.smoothScrollTo(max(0, c.left - dp(60)), 0) }
        }
    }

    private fun focusApp(a: AppEntry) {
        val i = Hub.apps.indexOf(a)
        if (i < 0) return
        Hub.grid = false
        selectIndex(i)
        Hub.save()
    }

    private fun toggleGrid() {
        Hub.grid = !Hub.grid
        applyLayoutState()
        Hub.save()
    }

    private fun reloadCurrent() {
        val a = currentApp()
        val w = a?.web
        if (a == null || w == null) {
            toast("No app is open")
            return
        }
        a.hadError = false
        a.failedAt = 0L
        w.reload()
        toast("Reloading " + a.name)
    }

    private fun closeCurrent() {
        val a = currentApp()
        if (a == null) {
            toast("No app is open")
            return
        }
        requestClose(a)
    }

    private fun requestClose(a: AppEntry) {
        if (!Hub.confirmClose) {
            doClose(a)
            return
        }
        AlertDialog.Builder(this)
            .setTitle("Close \"" + a.name + "\"?")
            .setMessage("This app will stop running and its current state will be lost.")
            .setPositiveButton("Close app") { _, _ -> doClose(a) }
            .setNegativeButton("Keep it", null)
            .show()
    }

    private fun doClose(a: AppEntry) {
        Hub.closeApp(a)
        structureChanged()
    }

    private fun confirmCloseAll() {
        if (Hub.apps.isEmpty()) {
            toast("No apps are open")
            return
        }
        AlertDialog.Builder(this)
            .setTitle("Close ALL apps?")
            .setMessage("Every app will stop running.")
            .setPositiveButton("Close all") { _, _ ->
                val copy = ArrayList<AppEntry>(Hub.apps)
                for (a in copy) Hub.closeApp(a)
                structureChanged()
            }
            .setNegativeButton("Cancel", null)
            .show()
    }

    // ---------------- dialogs ----------------

    fun showEditDialog(app: AppEntry?) {
        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        box.setPadding(dp(20), dp(8), dp(20), 0)
        val etName = EditText(this)
        etName.hint = "Name (optional)"
        etName.setSingleLine(true)
        val etUrl = EditText(this)
        etUrl.hint = "Address, e.g. web.whatsapp.com"
        etUrl.setSingleLine(true)
        etUrl.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_VARIATION_URI
        val cb = CheckBox(this)
        cb.text = "Request desktop site"
        if (app != null) {
            etName.setText(app.name)
            etUrl.setText(app.url)
            cb.isChecked = app.desktop
        }
        box.addView(etName, LinearLayout.LayoutParams(MP, WC))
        box.addView(etUrl, LinearLayout.LayoutParams(MP, WC))
        box.addView(cb, LinearLayout.LayoutParams(MP, WC))
        val d = AlertDialog.Builder(this)
            .setTitle(if (app == null) "Open a new app" else "Edit app")
            .setView(box)
            .setPositiveButton(if (app == null) "Open" else "Save") { _, _ ->
                onEditConfirmed(app, etName.text.toString(), etUrl.text.toString(), cb.isChecked)
            }
            .setNegativeButton("Cancel", null)
            .create()
        d.window?.setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_STATE_VISIBLE)
        d.show()
        etUrl.requestFocus()
    }

    private fun onEditConfirmed(app: AppEntry?, nameIn: String, urlIn: String, desktop: Boolean) {
        val url = normalizeUrl(urlIn)
        if (url.isEmpty()) {
            toast("Please enter an address")
            return
        }
        var name = nameIn.trim()
        if (name.isEmpty()) name = hostOf(url)
        if (app == null) {
            val added = Hub.addApp(name, url, desktop, 0L)
            if (added == null) {
                toast("Limit is " + MAX_APPS + " apps. Close one first.")
                return
            }
            structureChanged()
            selectIndex(Hub.apps.size - 1)
        } else {
            val urlChanged = url != app.url
            val deskChanged = desktop != app.desktop
            app.name = name
            app.url = url
            app.desktop = desktop
            val w = app.web
            if (w != null) {
                if (deskChanged) Hub.applyUa(w, desktop)
                if (urlChanged) {
                    app.curUrl = url
                    w.loadUrl(url)
                } else if (deskChanged) {
                    w.reload()
                }
            }
            structureChanged()
        }
    }

    private fun showPresets() {
        val names = Array(PRESETS.size) { PRESETS[it].name }
        val checked = BooleanArray(PRESETS.size)
        AlertDialog.Builder(this)
            .setTitle("Add popular apps")
            .setMultiChoiceItems(names, checked) { _, which, isChecked -> checked[which] = isChecked }
            .setPositiveButton("Add") { _, _ ->
                val firstNew = Hub.apps.size
                var added = 0
                var skipped = 0
                var delay = 0L
                for (i in PRESETS.indices) {
                    if (!checked[i]) continue
                    val p = PRESETS[i]
                    if (Hub.addApp(p.name, p.url, p.desktop, delay) != null) {
                        added++
                        delay += 500L
                    } else {
                        skipped++
                    }
                }
                if (added > 0) {
                    structureChanged()
                    selectIndex(firstNew)
                }
                if (skipped > 0) toast("Limit is " + MAX_APPS + " apps")
            }
            .setNegativeButton("Cancel", null)
            .show()
    }

    fun showAppOptions() {
        val a = currentApp()
        if (a == null) {
            toast("No app is open")
            return
        }
        val labels = arrayOf(
            "Edit name / address...",
            "Desktop site: " + onOff(a.desktop),
            "Go to start page",
            "Use current page as start page",
            "Back",
            "Forward"
        )
        AlertDialog.Builder(this)
            .setTitle(a.name)
            .setItems(labels) { _, which ->
                val w = a.web
                when (which) {
                    0 -> showEditDialog(a)
                    1 -> {
                        a.desktop = !a.desktop
                        if (w != null) {
                            Hub.applyUa(w, a.desktop)
                            w.reload()
                        }
                        Hub.save()
                    }
                    2 -> {
                        if (w != null) w.loadUrl(a.url)
                    }
                    3 -> {
                        val cur = w?.url
                        if (cur != null && cur.startsWith("http")) {
                            a.url = cur
                            Hub.save()
                            toast("Start page saved")
                        }
                    }
                    4 -> {
                        if (w != null && w.canGoBack()) w.goBack()
                    }
                    5 -> {
                        if (w != null && w.canGoForward()) w.goForward()
                    }
                    else -> {
                    }
                }
            }
            .show()
    }

    private fun showMore() {
        val labels = arrayOf(
            "Add popular apps...",
            "Current app options...",
            "Keep screen on: " + onOff(Hub.keepScreen),
            "Keep running in background: " + onOff(Hub.keepBg),
            "Hidden apps: " + (if (Hub.throttle) "throttled (saves battery)" else "fully active"),
            "Confirm before closing: " + onOff(Hub.confirmClose),
            "Grid columns: " + (if (Hub.cols == 0) "auto" else Hub.cols.toString()),
            "Allow unrestricted battery use...",
            "Keyboard and mouse help...",
            "Close ALL apps..."
        )
        AlertDialog.Builder(this)
            .setTitle("More")
            .setItems(labels) { _, which ->
                when (which) {
                    0 -> showPresets()
                    1 -> showAppOptions()
                    2 -> {
                        Hub.keepScreen = !Hub.keepScreen
                        applyKeepScreen()
                        Hub.save()
                        toast("Keep screen on: " + onOff(Hub.keepScreen))
                    }
                    3 -> {
                        Hub.keepBg = !Hub.keepBg
                        updateService()
                        Hub.save()
                        toast("Keep running in background: " + onOff(Hub.keepBg))
                    }
                    4 -> {
                        Hub.throttle = !Hub.throttle
                        applyLayoutState()
                        Hub.save()
                        toast(if (Hub.throttle) "Hidden apps are throttled" else "Hidden apps stay fully active")
                    }
                    5 -> {
                        Hub.confirmClose = !Hub.confirmClose
                        Hub.save()
                        toast("Confirm before closing: " + onOff(Hub.confirmClose))
                    }
                    6 -> {
                        Hub.cols = (Hub.cols + 1) % 7
                        applyLayoutState()
                        Hub.save()
                        toast("Grid columns: " + (if (Hub.cols == 0) "auto" else Hub.cols.toString()))
                    }
                    7 -> batterySettings()
                    8 -> showHelp()
                    9 -> confirmCloseAll()
                    else -> {
                    }
                }
            }
            .show()
    }

    private fun batterySettings() {
        try {
            val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
            if (pm.isIgnoringBatteryOptimizations(packageName)) {
                toast("Already unrestricted")
                return
            }
            val i = Intent(Settings.ACTION_REQUEST_IGNORE_BATTERY_OPTIMIZATIONS)
            i.data = Uri.parse("package:" + packageName)
            startActivity(i)
        } catch (e: Exception) {
            try {
                startActivity(Intent(Settings.ACTION_IGNORE_BATTERY_OPTIMIZATION_SETTINGS))
            } catch (e2: Exception) {
            }
        }
    }

    private fun showHelp() {
        val msg = "Ctrl+T  open a new app\n" +
            "Ctrl+W  close current app\n" +
            "Ctrl+Tab  next app (add Shift = previous)\n" +
            "Ctrl+1..9 or Alt+1..9  jump to app 1-9\n" +
            "Ctrl+G  grid / tabs view\n" +
            "Ctrl+R or F5  reload current app\n" +
            "Alt+Left / Alt+Right  back / forward\n" +
            "Ctrl+M  More menu\n\n" +
            "Mouse: wheel scrolls the page; wheel over the tab bar scrolls the tabs; " +
            "right-click a tab or tile title for its options.\n\n" +
            "Touch: long-press a tab or tile title for its options.\n\n" +
            "The Back button never closes an app: it goes back inside the page, or hides Alive Apps. " +
            "Apps only close with the Close button / x."
        AlertDialog.Builder(this)
            .setTitle("Keyboard and mouse")
            .setMessage(msg)
            .setPositiveButton("OK", null)
            .show()
    }

    // ---------------- first-run prompts ----------------

    private fun startupPrompts() {
        if (Build.VERSION.SDK_INT >= 33 && !Hub.askedNotif &&
            checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS) != PackageManager.PERMISSION_GRANTED
        ) {
            Hub.askedNotif = true
            Hub.save()
            try {
                requestPermissions(arrayOf(Manifest.permission.POST_NOTIFICATIONS), REQ_NOTIF)
                return
            } catch (e: Exception) {
            }
        }
        maybeShowPresets()
    }

    private fun maybeShowPresets() {
        if (Hub.firstRun && Hub.apps.isEmpty()) {
            Hub.firstRun = false
            Hub.save()
            showPresets()
        }
    }
}
