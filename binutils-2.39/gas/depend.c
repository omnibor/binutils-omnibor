/* depend.c - Handle dependency tracking.
   Copyright (C) 1997-2022 Free Software Foundation, Inc.

   This file is part of GAS, the GNU Assembler.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GAS; see the file COPYING.  If not, write to the Free
   Software Foundation, 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

#include "as.h"
#include "filenames.h"
#include "sha1.h"
#include "sha256.h"
#include <dirent.h>

#define GITOID_LENGTH_SHA1 20
#define GITOID_LENGTH_SHA256 32
#define MAX_FILE_SIZE_STRING_LENGTH 256

/* The file to write to, or NULL if no dependencies being kept
   (it can also be NULL if the OmniBOR information calculation
   is enabled, which inherently enables keeping dependencies,
   but it does not have to be NULL in such case).  */
static char * dep_file = NULL;

struct dependency
{
  char * file;
  struct dependency * next;
};

/* All the files we depend on.  */
static struct dependency * dep_chain = NULL;

/* Flag which indicates whether the OmniBOR information calculation
   is enabled or not.  */
static bool omnibor_enabled = false;

/* Current column in output file.  */
static int column = 0;

static int quote_string_for_make (FILE *, const char *);
static void wrap_output (FILE *, const char *, int);

/* Number of columns allowable.  */
#define MAX_COLUMNS 72

/* Start saving dependencies, to be written to FILENAME.  If this is
   never called, then dependency tracking is simply skipped (unless
   the OmniBOR information calculation is enabled - see
   omnibor_start_dependencies function).  */

void
start_dependencies (char *filename)
{
  dep_file = filename;
}

/* Another way to start saving dependencies.  If neither this nor
   start_dependencies function is called, then dependency
   tracking is simply skipped.  This function just enables
   the tracking of dependencies, but they cannot be written in
   a file later on, unless start_dependencies function is called
   as well.  */

void
omnibor_start_dependencies (void)
{
  omnibor_enabled = true;
}

/*  Check whether the OmniBOR calculation is enabled or not.  */

bool
is_omnibor_enabled (void)
{
  return omnibor_enabled;
}

/* Noticed a new filename, so try to register it.  */

void
register_dependency (const char *filename)
{
  struct dependency *dep;

  if (dep_file == NULL && !omnibor_enabled)
    return;

  for (dep = dep_chain; dep != NULL; dep = dep->next)
    {
      if (!filename_cmp (filename, dep->file))
	return;
    }

  dep = XNEW (struct dependency);
  dep->file = xstrdup (filename);
  dep->next = dep_chain;
  dep_chain = dep;
}

/* Quote a file name the way `make' wants it, and print it to FILE.
   If FILE is NULL, do no printing, but return the length of the
   quoted string.

   This code is taken from gcc with only minor changes.  */

static int
quote_string_for_make (FILE *file, const char *src)
{
  const char *p = src;
  int i = 0;

  for (;;)
    {
      char c = *p++;

      switch (c)
	{
	case '\0':
	case ' ':
	case '\t':
	  {
	    /* GNU make uses a weird quoting scheme for white space.
	       A space or tab preceded by 2N+1 backslashes represents
	       N backslashes followed by space; a space or tab
	       preceded by 2N backslashes represents N backslashes at
	       the end of a file name; and backslashes in other
	       contexts should not be doubled.  */
	    const char *q;

	    for (q = p - 1; src < q && q[-1] == '\\'; q--)
	      {
		if (file)
		  putc ('\\', file);
		i++;
	      }
	  }
	  if (!c)
	    return i;
	  if (file)
	    putc ('\\', file);
	  i++;
	  goto ordinary_char;

	case '$':
	  if (file)
	    putc (c, file);
	  i++;
	  /* Fall through.  */
	  /* This can mishandle things like "$(" but there's no easy fix.  */
	default:
	ordinary_char:
	  /* This can mishandle characters in the string "\0\n%*?[\\~";
	     exactly which chars are mishandled depends on the `make' version.
	     We know of no portable solution for this;
	     even GNU make 3.76.1 doesn't solve the problem entirely.
	     (Also, '\0' is mishandled due to our calling conventions.)  */
	  if (file)
	    putc (c, file);
	  i++;
	  break;
	}
    }
}

/* Append some output to the file, keeping track of columns and doing
   wrapping as necessary.  */

static void
wrap_output (FILE *f, const char *string, int spacer)
{
  int len = quote_string_for_make (NULL, string);

  if (len == 0)
    return;

  if (column
      && (MAX_COLUMNS
	  - 1 /* spacer */
	  - 2 /* ` \'   */
	  < column + len))
    {
      fprintf (f, " \\\n ");
      column = 0;
      if (spacer == ' ')
	spacer = '\0';
    }

  if (spacer == ' ')
    {
      putc (spacer, f);
      ++column;
    }

  quote_string_for_make (f, string);
  column += len;

  if (spacer == ':')
    {
      putc (spacer, f);
      ++column;
    }
}

/* Print dependency file.  */

void
print_dependencies (void)
{
  FILE *f;
  struct dependency *dep;

  if (dep_file == NULL)
    return;

  f = fopen (dep_file, FOPEN_WT);
  if (f == NULL)
    {
      as_warn (_("can't open `%s' for writing"), dep_file);
      return;
    }

  column = 0;
  wrap_output (f, out_file_name, ':');
  for (dep = dep_chain; dep != NULL; dep = dep->next)
    wrap_output (f, dep->file, ' ');

  putc ('\n', f);

  if (fclose (f))
    as_warn (_("can't close `%s'"), dep_file);
}

/* OmniBOR struct which contains the names of the directories from the path
   to the directory where the OmniBOR information is to be stored.  */

struct omnibor_dirs
{
  struct omnibor_dirs *next;
  DIR *dir;
};

static struct omnibor_dirs *omnibor_dirs_head, *omnibor_dirs_tail;

static void
omnibor_add_to_dirs (DIR **directory)
{
  struct omnibor_dirs *elem
    = (struct omnibor_dirs *) xmalloc (sizeof (*elem));
  elem->dir = *directory;
  elem->next = NULL;
  if (omnibor_dirs_head == NULL)
    omnibor_dirs_head = elem;
  else
    omnibor_dirs_tail->next = elem;
  omnibor_dirs_tail = elem;
}

/* Return the position of the first occurrence after start_pos position
   of char c in str string (start_pos is the first position to check).  */

static int
omnibor_find_char_from_pos (unsigned start_pos, char c, const char *str)
{
  for (unsigned ix = start_pos; ix < strlen (str); ix++)
    if (str[ix] == c)
      return ix;

  return -1;
}

/* Append the string str2 to the end of the string str1.  */

static void
omnibor_append_to_string (char **str1, const char *str2,
			 unsigned long len1, unsigned long len2)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len1 + len2 + 1));
  memcpy (*str1 + len1, str2, len2);
  (*str1)[len1 + len2] = '\0';
}

/* Add the string str2 as a prefix to the string str1.  */

static void
omnibor_add_prefix_to_string (char **str1, const char *str2)
{
  unsigned len1 = strlen (*str1), len2 = strlen (str2);
  char *temp = (char *) xcalloc
	(len1 + len2 + 1, sizeof (char));
  memcpy (temp, str2, len2);
  memcpy (temp + len2, *str1, len1);
  temp[len1 + len2] = '\0';
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len1 + len2 + 1));
  memcpy (*str1, temp, len1 + len2);
  (*str1)[len1 + len2] = '\0';
  free (temp);
}

/* Get the substring of length len of the str2 string starting from
   the start position and put it in the str1 string.  */

static void
omnibor_substr (char **str1, unsigned start, unsigned len, const char *str2)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len + 1));
  memcpy (*str1, str2 + start, len);
  (*str1)[len] = '\0';
}

/* Set the string str1 to have the contents of the string str2.  */

void
omnibor_set_contents (char **str1, const char *str2, unsigned long len)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len + 1));
  memcpy (*str1, str2, len);
  (*str1)[len] = '\0';
}

/* Open all the directories from the path specified in the res_dir
   parameter and put them in the omnibor_dirs_head list.  Also, create
   the directories which do not already exist.  */

static DIR *
open_all_directories_in_path (const char *res_dir)
{
  char *path = (char *) xcalloc (1, sizeof (char));
  char *dir_name = (char *) xcalloc (1, sizeof (char));

  int old_p = 0, p = omnibor_find_char_from_pos (0, '/', res_dir);
  int dfd, absolute = 0;
  DIR *dir = NULL;

  if (p == -1)
    {
      free (dir_name);
      free (path);
      return NULL;
    }
  /* If the res_dir is an absolute path.  */
  else if (p == 0)
    {
      absolute = 1;
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      /* Opening a root directory because an absolute path is specified.  */
      dir = opendir (path);
      dfd = dirfd (dir);

      omnibor_add_to_dirs (&dir);
      p = p + 1;
      old_p = p;

      /* Path is of format "/<dir>" where <dir> does not exist.  This point can be
         reached only if <dir> could not be created in the root folder, so it is
         considered as an illegal path.  */
      if ((p = omnibor_find_char_from_pos (p, '/', res_dir)) == -1)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}

      /* Process sequences of adjacent occurrences of character '/'.  */
      while (old_p == p)
        {
          p = p + 1;
          old_p = p;
          p = omnibor_find_char_from_pos (p, '/', res_dir);
        }

      if (p == -1)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}
    }

  omnibor_substr (&dir_name, old_p, p - old_p, res_dir);
  omnibor_append_to_string (&path, dir_name, strlen (path), strlen (dir_name));

  if ((dir = opendir (path)) == NULL)
    {
      if (absolute)
        mkdirat (dfd, dir_name, S_IRWXU);
      else
        mkdir (dir_name, S_IRWXU);
      dir = opendir (path);
    }

  if (dir == NULL)
    {
      free (dir_name);
      free (path);
      return NULL;
    }

  dfd = dirfd (dir);

  omnibor_add_to_dirs (&dir);
  p = p + 1;
  old_p = p;

  while ((p = omnibor_find_char_from_pos (p, '/', res_dir)) != -1)
    {
      /* Process sequences of adjacent occurrences of character '/'.  */
      while (old_p == p)
        {
          p = p + 1;
          old_p = p;
          p = omnibor_find_char_from_pos (p, '/', res_dir);
        }

      if (p == -1)
        break;

      omnibor_substr (&dir_name, old_p, p - old_p, res_dir);
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      omnibor_append_to_string (&path, dir_name, strlen (path),
				strlen (dir_name));

      if ((dir = opendir (path)) == NULL)
        {
          mkdirat (dfd, dir_name, S_IRWXU);
          dir = opendir (path);
        }

      if (dir == NULL)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}

      dfd = dirfd (dir);

      omnibor_add_to_dirs (&dir);
      p = p + 1;
      old_p = p;
    }

  if ((unsigned) old_p < strlen (res_dir))
    {
      omnibor_substr (&dir_name, old_p, strlen (res_dir) - old_p, res_dir);
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      omnibor_append_to_string (&path, dir_name, strlen (path),
				strlen (dir_name));

      if ((dir = opendir (path)) == NULL)
        {
          mkdirat (dfd, dir_name, S_IRWXU);
          dir = opendir (path);
        }

      omnibor_add_to_dirs (&dir);
    }

  free (dir_name);
  free (path);
  return dir;
}

/* Close all the directories from the omnibor_dirs_head list.  This function
   should be called after calling the function open_all_directories_in_path.  */

static void
close_all_directories_in_path (void)
{
  struct omnibor_dirs *dir = omnibor_dirs_head, *old = NULL;
  while (dir != NULL)
    {
      closedir (dir->dir);
      old = dir;
      dir = dir->next;
      free (old);
    }

  omnibor_dirs_head = NULL;
  omnibor_dirs_tail = NULL;
}

/* Calculate the SHA1 gitoid using the contents of the given file.  */

static void
calculate_sha1_omnibor (FILE *dependency_file, unsigned char resblock[])
{
  fseek (dependency_file, 0L, SEEK_END);
  long file_size = ftell (dependency_file);
  fseek (dependency_file, 0L, SEEK_SET);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  char *file_contents = (char *) xcalloc (file_size, sizeof (char));
  fread (file_contents, 1, file_size, dependency_file);

  /* Calculate the hash.  */
  struct sha1_ctx ctx;

  sha1_init_ctx (&ctx);

  sha1_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha1_process_bytes (file_contents, file_size, &ctx);

  sha1_finish_ctx (&ctx, resblock);

  free (file_contents);
  free (init_data);
}

/* Calculate the SHA1 gitoid using the given contents.  */

static void
calculate_sha1_omnibor_with_contents (char *contents,
				      unsigned char resblock[])
{
  long file_size = strlen (contents);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  /* Calculate the hash.  */
  struct sha1_ctx ctx;

  sha1_init_ctx (&ctx);

  sha1_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha1_process_bytes (contents, file_size, &ctx);

  sha1_finish_ctx (&ctx, resblock);

  free (init_data);
}

/* Calculate the SHA256 gitoid using the contents of the given file.  */

static void
calculate_sha256_omnibor (FILE *dependency_file, unsigned char resblock[])
{
  fseek (dependency_file, 0L, SEEK_END);
  long file_size = ftell (dependency_file);
  fseek (dependency_file, 0L, SEEK_SET);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  char *file_contents = (char *) xcalloc (file_size, sizeof (char));
  fread (file_contents, 1, file_size, dependency_file);

  /* Calculate the hash.  */
  struct sha256_ctx ctx;

  sha256_init_ctx (&ctx);

  sha256_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha256_process_bytes (file_contents, file_size, &ctx);

  sha256_finish_ctx (&ctx, resblock);

  free (file_contents);
  free (init_data);
}

/* Calculate the SHA256 gitoid using the given contents.  */

static void
calculate_sha256_omnibor_with_contents (char *contents,
					unsigned char resblock[])
{
  long file_size = strlen (contents);

  /* This length should be enough for everything up to 64B, which should
     cover long type.  */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  /* Calculate the hash.  */
  struct sha256_ctx ctx;

  sha256_init_ctx (&ctx);

  sha256_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha256_process_bytes (contents, file_size, &ctx);

  sha256_finish_ctx (&ctx, resblock);

  free (init_data);
}

/* OmniBOR dependency file struct which contains its SHA1 gitoid, its SHA256
   gitoid and its filename.  */

struct omnibor_deps
{
  struct omnibor_deps *next;
  char *sha1_contents;
  char *sha256_contents;
  char *name;
};

static struct omnibor_deps *omnibor_deps_head, *omnibor_deps_tail;

static void
omnibor_add_to_deps (char *filename, char *sha1_contents, char *sha256_contents,
		     unsigned long sha1_contents_len,
		     unsigned long sha256_contents_len)
{
  struct omnibor_deps *elem
    = (struct omnibor_deps *) xmalloc (sizeof (*elem));
  elem->name = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&elem->name, filename, strlen (elem->name),
			    strlen (filename));
  if (sha1_contents != NULL)
    {
      elem->sha1_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha1_contents, sha1_contents,
				strlen (elem->sha1_contents),
				sha1_contents_len);
    }
  else
    elem->sha1_contents = NULL;
  if (sha256_contents != NULL)
    {
      elem->sha256_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha256_contents, sha256_contents,
				strlen (elem->sha256_contents),
				sha256_contents_len);
    }
  else
    elem->sha256_contents = NULL;
  elem->next = NULL;
  if (omnibor_deps_head == NULL)
    omnibor_deps_head = elem;
  else
    omnibor_deps_tail->next = elem;
  omnibor_deps_tail = elem;
}

void
omnibor_clear_deps (void)
{
  struct omnibor_deps *dep = omnibor_deps_head, *old = NULL;
  while (dep != NULL)
    {
      free (dep->name);
      if (dep->sha1_contents)
        free (dep->sha1_contents);
      if (dep->sha256_contents)
        free (dep->sha256_contents);
      old = dep;
      dep = dep->next;
      free (old);
    }

  omnibor_deps_head = NULL;
  omnibor_deps_tail = NULL;
}

static struct omnibor_deps *
omnibor_is_dep_present (const char *name)
{
  struct omnibor_deps *dep;
  for (dep = omnibor_deps_head; dep != NULL; dep = dep->next)
    if (strcmp (name, dep->name) == 0)
      return dep;

  return NULL;
}

/* Sort the contents of the OmniBOR Document file using the selection sort
   algorithm.  The parameter ind should be either 0 (sort the SHA1 OmniBOR
   Document file) or 1 (sort the SHA256 OmniBOR Document file).  */

static void
omnibor_sort (unsigned int ind)
{
  if (omnibor_deps_head == NULL || omnibor_deps_head->next == NULL
      || (ind != 0 && ind != 1))
    return;

  struct omnibor_deps *dep1, *dep2, *curr;
  for (dep1 = omnibor_deps_head; dep1 != NULL; dep1 = dep1->next)
    {
      curr = dep1;
      for (dep2 = dep1->next; dep2 != NULL; dep2 = dep2->next)
        {
          if ((dep1->sha1_contents == NULL && dep2->sha1_contents != NULL)
               || (dep1->sha1_contents != NULL && dep2->sha1_contents == NULL)
               || (dep1->sha256_contents == NULL && dep2->sha256_contents != NULL)
               || (dep1->sha256_contents != NULL && dep2->sha256_contents == NULL))
            return;
          if ((ind == 0 && strcmp (curr->sha1_contents, dep2->sha1_contents) > 0)
               || (ind == 1
		   && strcmp (curr->sha256_contents, dep2->sha256_contents) > 0))
            curr = dep2;
        }

      if (strcmp (curr->name, dep1->name) != 0)
        {
	  char *temp_name = (char *) xcalloc (1, sizeof (char));
	  char *temp_sha1_contents = NULL;
	  if (dep1->sha1_contents != NULL)
	    temp_sha1_contents = (char *) xcalloc (1, sizeof (char));
	  char *temp_sha256_contents = NULL;
	  if (dep1->sha256_contents != NULL)
	    temp_sha256_contents = (char *) xcalloc (1, sizeof (char));

          omnibor_set_contents (&temp_name, dep1->name,
				strlen (dep1->name));
          if (dep1->sha1_contents != NULL)
            omnibor_set_contents (&temp_sha1_contents, dep1->sha1_contents,
				  2 * GITOID_LENGTH_SHA1);
          if (dep1->sha256_contents != NULL)
	    omnibor_set_contents (&temp_sha256_contents, dep1->sha256_contents,
				  2 * GITOID_LENGTH_SHA256);

          omnibor_set_contents (&dep1->name, curr->name,
				strlen (curr->name));
          if (dep1->sha1_contents != NULL)
	    omnibor_set_contents (&dep1->sha1_contents, curr->sha1_contents,
				  2 * GITOID_LENGTH_SHA1);
          if (dep1->sha256_contents != NULL)
	    omnibor_set_contents (&dep1->sha256_contents, curr->sha256_contents,
				  2 * GITOID_LENGTH_SHA256);

          omnibor_set_contents (&curr->name, temp_name,
				strlen (temp_name));
          if (dep1->sha1_contents != NULL)
	    omnibor_set_contents (&curr->sha1_contents, temp_sha1_contents,
				  2 * GITOID_LENGTH_SHA1);
          if (dep1->sha256_contents != NULL)
	    omnibor_set_contents (&curr->sha256_contents, temp_sha256_contents,
				  2 * GITOID_LENGTH_SHA256);

	  if (dep1->sha256_contents != NULL)
	    free (temp_sha256_contents);
	  if (dep1->sha1_contents != NULL)
	    free (temp_sha1_contents);
	  free (temp_name);
        }
    }
}

/* OmniBOR ".note.omnibor" section struct which contains the filename of the
   dependency and the contents of its ".note.omnibor" section (the SHA1 gitoid
   and the SHA256 gitoid).  */

struct omnibor_note_sections
{
  struct omnibor_note_sections *next;
  char *name;
  char *sha1_contents;
  char *sha256_contents;
};

struct omnibor_note_sections *omnibor_note_sections_head,
			     *omnibor_note_sections_tail;

void
omnibor_add_to_note_sections (const char *filename, char *sha1_sec_contents,
			      char *sha256_sec_contents,
			      unsigned long sha1_sec_contents_len,
			      unsigned long sha256_sec_contents_len)
{
  struct omnibor_note_sections *elem
    = (struct omnibor_note_sections *) xmalloc (sizeof (*elem));
  elem->name = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&elem->name, filename, strlen (elem->name),
			    strlen (filename));
  if (sha1_sec_contents != NULL)
    {
      elem->sha1_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha1_contents, sha1_sec_contents,
				strlen (elem->sha1_contents),
				sha1_sec_contents_len);
    }
  else
    elem->sha1_contents = NULL;
  if (sha256_sec_contents != NULL)
    {
      elem->sha256_contents = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&elem->sha256_contents, sha256_sec_contents,
				strlen (elem->sha256_contents),
				sha256_sec_contents_len);
    }
  else
    elem->sha256_contents = NULL;
  elem->next = NULL;
  if (omnibor_note_sections_head == NULL)
    omnibor_note_sections_head = elem;
  else
    omnibor_note_sections_tail->next = elem;
  omnibor_note_sections_tail = elem;
}

void
omnibor_clear_note_sections (void)
{
  struct omnibor_note_sections *dep = omnibor_note_sections_head, *old = NULL;
  while (dep != NULL)
    {
      free (dep->name);
      if (dep->sha1_contents)
        free (dep->sha1_contents);
      if (dep->sha256_contents)
        free (dep->sha256_contents);
      old = dep;
      dep = dep->next;
      free (old);
    }

  omnibor_note_sections_head = NULL;
  omnibor_note_sections_tail = NULL;
}

/* If the dependency with the given name is not in the omnibor_note_sections_head
   list, return NULL.  Otherwise, return the SHA1 gitoid (hash_func_type == 0)
   or the SHA256 gitoid (hash_func_type == 1) for that dependency.  If any value
   other than 0 or 1 is passed in hash_func_type, the behaviour is undefined.  */

static char *
omnibor_is_note_section_present (const char *name, unsigned hash_func_type)
{
  struct omnibor_note_sections *note;
  for (note = omnibor_note_sections_head; note != NULL; note = note->next)
    if (strcmp (name, note->name) == 0)
      {
        if (hash_func_type == 0)
          return note->sha1_contents;
        else if (hash_func_type == 1)
          return note->sha256_contents;
        /* This point should never be reached.  */
        else
          return NULL;
      }

  return NULL;
}

/* Store the OmniBOR information in the specified directory whose path is
   written in the result_dir parameter.  The hash_size parameter has to be
   either GITOID_LENGTH_SHA1 (for the SHA1 OmniBOR information) or
   GITOID_LENGTH_SHA256 (for the SHA256 OmniBOR information).  If any error
   occurs during the creation of the OmniBOR Document file, name parameter
   is set to point to an empty string.  */

static void
create_omnibor_document_file (char **name, const char *result_dir,
			      char *new_file_contents, unsigned int new_file_size,
			      unsigned int hash_size)
{
  if (hash_size != GITOID_LENGTH_SHA1 && hash_size != GITOID_LENGTH_SHA256)
    {
      omnibor_set_contents (name, "", 0);
      return;
    }

  char *path_objects = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_objects, "objects", strlen (path_objects),
			    strlen ("objects"));
  DIR *dir_one = NULL;

  if (result_dir)
    {
      if ((dir_one = opendir (result_dir)) == NULL)
        {
          mkdir (result_dir, S_IRWXU);
	  dir_one = opendir (result_dir);
	}

      if (dir_one != NULL)
        {
          omnibor_add_prefix_to_string (&path_objects, "/");
          omnibor_add_prefix_to_string (&path_objects, result_dir);
          int dfd1 = dirfd (dir_one);
          mkdirat (dfd1, "objects", S_IRWXU);
        }
      else if (strlen (result_dir) != 0)
        {
          DIR *final_dir = open_all_directories_in_path (result_dir);
          /* If an error occurred, illegal path is detected and the OmniBOR
             information is not written.  */
          /* TODO: Maybe put a message here that a specified path, in which
	     the OmniBOR information should be stored, is illegal.  */
	  /* TODO: In case of an error, if any directories were created,
	     remove them.  */
          if (final_dir == NULL)
            {
              close_all_directories_in_path ();
              free (path_objects);
              omnibor_set_contents (name, "", 0);
              return;
            }
          else
            {
              omnibor_add_prefix_to_string (&path_objects, "/");
	      omnibor_add_prefix_to_string (&path_objects, result_dir);
              int dfd1 = dirfd (final_dir);
              mkdirat (dfd1, "objects", S_IRWXU);
            }
        }
      /* This point should not be reachable.  */
      else
	{
	  free (path_objects);
	  omnibor_set_contents (name, "", 0);
	  return;
	}
    }
  /* This point should not be reachable.  */
  else
    {
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  DIR *dir_two = opendir (path_objects);
  if (dir_two == NULL)
    {
      close_all_directories_in_path ();
      if (result_dir && dir_one)
        closedir (dir_one);
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  int dfd2 = dirfd (dir_two);

  char *path_sha = NULL;
  DIR *dir_three = NULL;
  if (hash_size == GITOID_LENGTH_SHA1)
    {
      mkdirat (dfd2, "gitoid_blob_sha1", S_IRWXU);

      path_sha = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&path_sha, path_objects, strlen (path_sha),
				strlen (path_objects));
      omnibor_append_to_string (&path_sha, "/gitoid_blob_sha1",
				strlen (path_sha),
				strlen ("/gitoid_blob_sha1"));
      dir_three = opendir (path_sha);
      if (dir_three == NULL)
        {
          closedir (dir_two);
          close_all_directories_in_path ();
          if (result_dir && dir_one)
            closedir (dir_one);
          free (path_sha);
          free (path_objects);
          omnibor_set_contents (name, "", 0);
          return;
        }
    }
  else
    {
      mkdirat (dfd2, "gitoid_blob_sha256", S_IRWXU);

      path_sha = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&path_sha, path_objects, strlen (path_sha),
				strlen (path_objects));
      omnibor_append_to_string (&path_sha, "/gitoid_blob_sha256",
				strlen (path_sha),
				strlen ("/gitoid_blob_sha256"));
      dir_three = opendir (path_sha);
      if (dir_three == NULL)
        {
          closedir (dir_two);
          close_all_directories_in_path ();
          if (result_dir && dir_one)
            closedir (dir_one);
          free (path_sha);
          free (path_objects);
          omnibor_set_contents (name, "", 0);
          return;
        }
    }

  int dfd3 = dirfd (dir_three);
  char *name_substr = (char *) xcalloc (1, sizeof (char));
  omnibor_substr (&name_substr, 0, 2, *name);
  mkdirat (dfd3, name_substr, S_IRWXU);

  char *path_dir = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_dir, path_sha, strlen (path_dir),
			    strlen (path_sha));
  omnibor_append_to_string (&path_dir, "/", strlen (path_dir),
			    strlen ("/"));

  /* Save current length of path_dir before characters from hash are added to
     the path.  This is done because the calculation of the length of the path
     from here moving forward is done manually by adding the length of the
     following parts of the path since hash can produce '\0' characters, so
     strlen is not good enough.  */
  unsigned long path_dir_temp_len = strlen (path_dir);

  omnibor_append_to_string (&path_dir, name_substr, path_dir_temp_len, 2);
  DIR *dir_four = opendir (path_dir);
  if (dir_four == NULL)
    {
      closedir (dir_three);
      closedir (dir_two);
      close_all_directories_in_path ();
      if (result_dir && dir_one)
        closedir (dir_one);
      free (path_dir);
      free (name_substr);
      free (path_sha);
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  char *new_file_path = (char *) xcalloc (1, sizeof (char));
  omnibor_substr (&name_substr, 2, 2 * hash_size - 2, *name);
  omnibor_append_to_string (&new_file_path, path_dir, strlen (new_file_path),
			    path_dir_temp_len + 2);
  omnibor_append_to_string (&new_file_path, "/", path_dir_temp_len + 2,
			    strlen ("/"));
  omnibor_append_to_string (&new_file_path, name_substr,
			    path_dir_temp_len + 2 + strlen ("/"),
			    2 * hash_size - 2);

  FILE *new_file = fopen (new_file_path, "w");
  if (new_file != NULL)
    {
      fwrite (new_file_contents, sizeof (char), new_file_size, new_file);
      fclose (new_file);
    }
  else
    omnibor_set_contents (name, "", 0);

  closedir (dir_four);
  closedir (dir_three);
  closedir (dir_two);
  close_all_directories_in_path ();
  if (result_dir && dir_one)
    closedir (dir_one);
  free (new_file_path);
  free (path_dir);
  free (name_substr);
  free (path_sha);
  free (path_objects);
}

/* Calculate the gitoids of all the dependencies of the resulting object file
   and create the OmniBOR Document file using them.  Then calculate the
   gitoid of that file and name it with that gitoid in the format specified
   by the OmniBOR specification.  Use SHA1 hashing algorithm for calculating
   all the gitoids.  */

void
write_sha1_omnibor (char **name, const char *result_dir)
{
  static const char *const lut = "0123456789abcdef";
  char *new_file_contents = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&new_file_contents, "gitoid:blob:sha1\n",
			    strlen (new_file_contents),
			    strlen ("gitoid:blob:sha1\n"));
  char *temp_file_contents = (char *) xcalloc (1, sizeof (char));
  char *high_ch = (char *) xmalloc (sizeof (char) * 2);
  high_ch[1] = '\0';
  char *low_ch = (char *) xmalloc (sizeof (char) * 2);
  low_ch[1] = '\0';

  struct omnibor_deps *curr_dep = NULL;
  struct dependency *dep;
  for (dep = dep_chain; dep != NULL; dep = dep->next)
    {
      if ((curr_dep = omnibor_is_dep_present (dep->file)) != NULL)
	if (curr_dep->sha1_contents != NULL)
	  continue;

      FILE *dep_file_handle = fopen (dep->file, "rb");
      if (dep_file_handle == NULL)
        continue;
      unsigned char resblock[GITOID_LENGTH_SHA1];

      calculate_sha1_omnibor (dep_file_handle, resblock);

      fclose (dep_file_handle);

      omnibor_set_contents (&temp_file_contents, "", 0);

      for (unsigned i = 0; i != GITOID_LENGTH_SHA1; i++)
        {
          high_ch[0] = lut[resblock[i] >> 4];
          low_ch[0] = lut[resblock[i] & 15];
          omnibor_append_to_string (&temp_file_contents, high_ch,
				    i * 2, 2);
          omnibor_append_to_string (&temp_file_contents, low_ch,
				    i * 2 + 1, 2);
        }

      if (curr_dep == NULL)
        omnibor_add_to_deps (dep->file, temp_file_contents, NULL,
			     2 * GITOID_LENGTH_SHA1, 0);
      /* Here curr_dep->sha1_contents has to be NULL.  */
      else
        {
          curr_dep->sha1_contents = (char *) xcalloc (1, sizeof (char));
	  omnibor_append_to_string (&curr_dep->sha1_contents,
				    temp_file_contents,
				    strlen (curr_dep->sha1_contents),
				    2 * GITOID_LENGTH_SHA1);
        }
    }

  omnibor_sort (0);

  unsigned current_length = strlen (new_file_contents);
  struct omnibor_deps *dependency_file;
  for (dependency_file = omnibor_deps_head; dependency_file != NULL;
       dependency_file = dependency_file->next)
    {
      omnibor_append_to_string (&new_file_contents, "blob ",
				current_length,
				strlen ("blob "));
      current_length += strlen ("blob ");
      omnibor_append_to_string (&new_file_contents, dependency_file->sha1_contents,
				current_length,
				2 * GITOID_LENGTH_SHA1);
      current_length += 2 * GITOID_LENGTH_SHA1;
      char *note_sec_contents =
		omnibor_is_note_section_present (dependency_file->name, 0);
      if (note_sec_contents != NULL)
        {
          omnibor_append_to_string (&new_file_contents, " bom ",
				    current_length,
				    strlen (" bom "));
          current_length += strlen (" bom ");
	  omnibor_append_to_string (&new_file_contents, note_sec_contents,
				    current_length,
				    2 * GITOID_LENGTH_SHA1);
          current_length += 2 * GITOID_LENGTH_SHA1;
        }
      omnibor_append_to_string (&new_file_contents, "\n",
				current_length,
				strlen ("\n"));
      current_length += strlen ("\n");
    }
  unsigned new_file_size = current_length;

  unsigned char resblock[GITOID_LENGTH_SHA1];
  calculate_sha1_omnibor_with_contents (new_file_contents, resblock);

  for (unsigned i = 0; i != GITOID_LENGTH_SHA1; i++)
    {
      high_ch[0] = lut[resblock[i] >> 4];
      low_ch[0] = lut[resblock[i] & 15];
      omnibor_append_to_string (name, high_ch, i * 2, 2);
      omnibor_append_to_string (name, low_ch, i * 2 + 1, 2);
    }
  free (low_ch);
  free (high_ch);

  create_omnibor_document_file (name, result_dir, new_file_contents,
				new_file_size, GITOID_LENGTH_SHA1);

  free (temp_file_contents);
  free (new_file_contents);
}

/* Calculate the gitoids of all the dependencies of the resulting object file
   and create the OmniBOR Document file using them.  Then calculate the
   gitoid of that file and name it with that gitoid in the format specified
   by the OmniBOR specification.  Use SHA256 hashing algorithm for calculating
   all the gitoids.  */

void
write_sha256_omnibor (char **name, const char *result_dir)
{
  static const char *const lut = "0123456789abcdef";
  char *new_file_contents = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&new_file_contents, "gitoid:blob:sha256\n",
			    strlen (new_file_contents),
			    strlen ("gitoid:blob:sha256\n"));
  char *temp_file_contents = (char *) xcalloc (1, sizeof (char));
  char *high_ch = (char *) xmalloc (sizeof (char) * 2);
  high_ch[1] = '\0';
  char *low_ch = (char *) xmalloc (sizeof (char) * 2);
  low_ch[1] = '\0';

  struct omnibor_deps *curr_dep = NULL;
  struct dependency *dep;
  for (dep = dep_chain; dep != NULL; dep = dep->next)
    {
      if ((curr_dep = omnibor_is_dep_present (dep->file)) != NULL)
	if (curr_dep->sha256_contents != NULL)
	  continue;

      FILE *dep_file_handle = fopen (dep->file, "rb");
      if (dep_file_handle == NULL)
        continue;
      unsigned char resblock[GITOID_LENGTH_SHA256];

      calculate_sha256_omnibor (dep_file_handle, resblock);

      fclose (dep_file_handle);

      omnibor_set_contents (&temp_file_contents, "", 0);

      for (unsigned i = 0; i != GITOID_LENGTH_SHA256; i++)
        {
          high_ch[0] = lut[resblock[i] >> 4];
          low_ch[0] = lut[resblock[i] & 15];
          omnibor_append_to_string (&temp_file_contents, high_ch,
				    i * 2, 2);
          omnibor_append_to_string (&temp_file_contents, low_ch,
				    i * 2 + 1, 2);
        }

      if (curr_dep == NULL)
        omnibor_add_to_deps (dep->file, NULL, temp_file_contents,
			     0, 2 * GITOID_LENGTH_SHA256);
      /* Here curr_dep->sha256_contents has to be NULL.  */
      else
        {
          curr_dep->sha256_contents = (char *) xcalloc (1, sizeof (char));
	  omnibor_append_to_string (&curr_dep->sha256_contents,
				    temp_file_contents,
				    strlen (curr_dep->sha256_contents),
				    2 * GITOID_LENGTH_SHA256);
        }
    }

  omnibor_sort (1);

  unsigned current_length = strlen (new_file_contents);
  struct omnibor_deps *dependency_file;
  for (dependency_file = omnibor_deps_head; dependency_file != NULL;
       dependency_file = dependency_file->next)
    {
      omnibor_append_to_string (&new_file_contents, "blob ",
				current_length,
				strlen ("blob "));
      current_length += strlen ("blob ");
      omnibor_append_to_string (&new_file_contents, dependency_file->sha256_contents,
				current_length,
				2 * GITOID_LENGTH_SHA256);
      current_length += 2 * GITOID_LENGTH_SHA256;
      char *note_sec_contents =
		omnibor_is_note_section_present (dependency_file->name, 1);
      if (note_sec_contents != NULL)
        {
          omnibor_append_to_string (&new_file_contents, " bom ",
				    current_length,
				    strlen (" bom "));
          current_length += strlen (" bom ");
	  omnibor_append_to_string (&new_file_contents, note_sec_contents,
				    current_length,
				    2 * GITOID_LENGTH_SHA256);
          current_length += 2 * GITOID_LENGTH_SHA256;
        }
      omnibor_append_to_string (&new_file_contents, "\n",
				current_length,
				strlen ("\n"));
      current_length += strlen ("\n");
    }
  unsigned new_file_size = current_length;

  unsigned char resblock[GITOID_LENGTH_SHA256];
  calculate_sha256_omnibor_with_contents (new_file_contents, resblock);

  for (unsigned i = 0; i != GITOID_LENGTH_SHA256; i++)
    {
      high_ch[0] = lut[resblock[i] >> 4];
      low_ch[0] = lut[resblock[i] & 15];
      omnibor_append_to_string (name, high_ch, i * 2, 2);
      omnibor_append_to_string (name, low_ch, i * 2 + 1, 2);
    }
  free (low_ch);
  free (high_ch);

  create_omnibor_document_file (name, result_dir, new_file_contents,
				new_file_size, GITOID_LENGTH_SHA256);

  free (temp_file_contents);
  free (new_file_contents);
}
