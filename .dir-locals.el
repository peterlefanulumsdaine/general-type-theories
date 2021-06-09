;; ((coq-mode
;;   . ((eval .
;;	   (progn
;;	     (make-local-variable 'coq-prog-args)
;;	     (setq coq-prog-args `("-emacs" "-noinit" "-indices-matter"
;;				  "-Q" ,(expand-file-name (locate-dominating-file buffer-file-name ".dir-locals.el")) "" )))))))
